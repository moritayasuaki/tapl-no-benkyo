#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <setjmp.h>
#include <ctype.h>
#include <assert.h>
#include <stdalign.h>
#include <limits.h>

#define generic     _Generic
#define info(...)   fprintf(stderr, __VA_ARGS__)
#define warn(...)   fprintf(stderr, __VA_ARGS__)
#define error(...)  (fprintf(stderr, __VA_ARGS__), exit(1))
#define debug(...)  (debug_file && fprintf(debug_file, __VA_ARGS__))
#define bug()       (error("%s:%d:%s() bug!\n", __FILE__, __LINE__, __func__))
#define lim_id_len  32
#define min_idx     (INT_MIN)
#define max_idx     (INT_MAX)

static_assert(sizeof(intptr_t) > sizeof(int), "pointer size is very small\n");

#define prolog      "+---------------+\n"\
                    "| TAPLE chap 4. |\n"\
                    "+---------------+\n"

#define epilog      "+---------------+\n"\
                    "|  good bye ;)  |\n"\
                    "+---------------+\n"

#define console     ">>> "

FILE *debug_file;
int interactive;
union term;
struct bind;

typedef struct {intptr_t raw;} ref_t;

struct ctx {
    int len;
    struct bind *top;
    FILE *log;
    FILE *buf;
    FILE *src;
    FILE *dst;
};

struct bind {
    ref_t def;
    ref_t type;
    fpos_t pos;
};

struct abs {
    ref_t exp;
    ref_t type;
    fpos_t pos;
};

struct app {
    ref_t fun;
    ref_t arg;
};

union term {
    struct abs abs;
    struct app app;
};

enum tag {
    tnum,
    tvar,
    tabs,
    tapp,
    thole = alignof(union term),
};


#define is_tnil(x) (((x).raw) == 0)
#define tnil (ref_t){0}
#define tsize  sizeof(union term)
#define talign alignof(union term)
static_assert(tapp < talign, "num of reference tag exceed pointer align\n");

int to_var(ref_t ref)
{
    return ref.raw;
}

struct abs* to_abs(ref_t ref)
{
    return (struct abs *)(ref.raw & -talign);
}

struct app* to_app(ref_t ref)
{
    return (struct app *)(ref.raw & -talign);
}

#define to_ref(x) generic((x),\
    struct abs*:    (ref_t){(intptr_t)(x) | tabs},\
    struct app*:    (ref_t){(intptr_t)(x) | tapp},\
    int:            (ref_t){(intptr_t)(x)},\
    default: tnil)

enum tag get_tag(ref_t ref)
{
    if (is_tnil(ref))
        return thole;
    if (min_idx <= ref.raw && ref.raw <= max_idx)
        return tvar;
    return ref.raw & ~-talign;
}

int is_eof(FILE *f)
{
    return ferror(f) || feof(f);
}

fpos_t save_pos(struct ctx *ctx)
{
    fpos_t pos;
    fgetpos(ctx->buf, &pos);
    return pos;
}

void restore_pos(struct ctx *ctx, fpos_t pos)
{
    fsetpos(ctx->buf, &pos);
}

void read_line(struct ctx *ctx)
{
    fpos_t save = save_pos(ctx);
    while (1) {
        int c = fgetc(ctx->src);
        if (c == EOF) {
            restore_pos(ctx, save);
            return;
        } else if (c == '\n') {
            fputc(c, ctx->buf);
            restore_pos(ctx, save);
            return;
        } else {
            fputc(c, ctx->buf);
        }
    }
}

int eat_char(struct ctx *ctx)
{
    if (is_eof(ctx->buf) && !interactive)
        read_line(ctx);
    int c = fgetc(ctx->buf);
    return c;
}

int undo_char(struct ctx *ctx, int c)
{
    return ungetc(c, ctx->buf);
}

int peek_char(struct ctx *ctx)
{
    return undo_char(ctx, eat_char(ctx));
}

int emit_str(struct ctx *ctx, char *str)
{
    return fputs(str, ctx->dst);
}

void skip_spaces(struct ctx *ctx)
{
    int c;
    do {
        c = eat_char(ctx);
    } while (isspace(c));
    undo_char(ctx, c);
}

int match_eol(struct ctx *ctx)
{
    int c;
    do {
        c = eat_char(ctx);
    } while (isspace(c) && c != '\n');
    if (c == '\n' || c == EOF)
        return 1;
    undo_char(ctx, c);
    return 0;
}

int match_num(struct ctx *ctx)
{
    int c;
    intptr_t i;
    fpos_t save = save_pos(ctx);
    c = eat_char(ctx);
    if (!isdigit(c)) {
        undo_char(ctx, c);
        return -1;
    }
    i = c - '0';
    while (1) {
        c = eat_char(ctx);
        if (!isdigit(c)) {
            undo_char(ctx, c);
            return i;
        }
        i = 10 * i + c - '0';
    }
}

int match_str(struct ctx *ctx, char *str)
{
    skip_spaces(ctx);
    fpos_t save = save_pos(ctx);
    while (*str)
        if (eat_char(ctx) != *str++)
            goto mismatch;
    return 1;
mismatch:
    restore_pos(ctx, save);
    return 0;
}

int match_id(struct ctx *ctx, char *id)
{
    skip_spaces(ctx);
    fpos_t save = save_pos(ctx);
    if (!match_str(ctx, id))
        goto mismatch;
    int c = eat_char(ctx);
    if (isalnum(c) || c == '_')
        goto mismatch;
    undo_char(ctx, c);
    return 1;
mismatch:
    restore_pos(ctx, save);
    return 0;
}

int match(struct ctx *ctx, char *s)
{
    skip_spaces(ctx);
    if (isalpha(*s) || *s == '_')
        return match_id(ctx, s);
    return match_str(ctx, s);
}

int is_keyword(char *id)
{
    return !strcmp(id, "in") ||
        !strcmp(id, "lambda") ||
        !strcmp(id, "let");
}

struct bind *get_base(struct ctx *ctx)
{
    return ctx->top + ctx->len;
}

char *get_id(struct ctx *ctx, char *id)
{
    skip_spaces(ctx);
    char *p = id;
    fpos_t save = save_pos(ctx);
    int c = eat_char(ctx);
    if (!(isalpha(c) || c == '_')) {
        undo_char(ctx, c);
        return NULL;
    }
    int l = 0;
    do {
        if (l < lim_id_len - 1)
            id[l] = c;
        c = eat_char(ctx);
        l++;
    } while (isalnum(c) || c == '_');
    if (l >= lim_id_len) {
        warn("too long identifier\n");
        l = lim_id_len - 1;
    }
    id[l] = '\0';
    undo_char(ctx, c);
    if (is_keyword(id)) {
        restore_pos(ctx, save);
        return NULL;
    }
    return id;
}

int find_bind_idx(struct ctx *ctx, char *id)
{
    int len = ctx->len;
    struct bind *base = get_base(ctx);
    fpos_t save = save_pos(ctx);
    for (int idx=1; idx <= len; idx++) {
        restore_pos(ctx, base[-idx].pos);
        if (match_id(ctx, id)) {
            restore_pos(ctx, save);
            return idx;
        }
    }
    restore_pos(ctx, save);
    return 0;
}

struct bind *get_bind(struct ctx *ctx, int idx)
{
    int len = ctx->len;
    struct bind *base = get_base(ctx);
    if (0 < idx && idx <= len)
        return &base[-idx];
    bug();
}

void push_bind(struct ctx *ctx, fpos_t pos)
{
    int len = ctx->len;
    struct bind *top = ctx->top;
    top = realloc(top, (len+1) * sizeof(struct bind));
    top[len].pos = pos;
    top[len].def = tnil;
    top[len].type = tnil;
    if (!top)
        error("no memeory\n");
    ctx->top = top;
    ctx->len = len+1;
}

void pop_bind(struct ctx *ctx)
{
    int len = ctx->len;
    struct bind *top = ctx->top;
    if (len-1) {
        top = realloc(top, (len-1) * sizeof(struct bind));
    } else {
        free(top);
        top = NULL;
    }
    ctx->top = top;
    ctx->len = len-1;
}

void discard(ref_t term);

ref_t parse_term(struct ctx *ctx, jmp_buf jb);

#define append_log(ctx, ...) (fprintf((ctx)->log, "%lld:",save_pos(ctx)), fprintf((ctx)->log, __VA_ARGS__), NULL)

void reset_log(struct ctx *ctx)
{
    ctx->log = tmpfile();
}

ref_t parse_abs(struct ctx *ctx, jmp_buf jb)
{
    char buf[lim_id_len];
    if (!match(ctx, "lambda")) {
        append_log(ctx, "expected 'lambda'\n");
        return tnil;
    }
    debug("%*c%s\n", ctx->len, ' ', __func__);
    skip_spaces(ctx);
    fpos_t pos = save_pos(ctx);
    if (!get_id(ctx, buf)) {
        append_log(ctx, "expected identifier\n");
        longjmp(jb, 1);
    }
    jmp_buf njb;
    ref_t type = tnil;
    ref_t exp = tnil;
    if (!setjmp(njb)) {
#if 0
        if (!match(ctx, ":")) {
            append_log(ctx, "expected ':'\n");
            longjmp(njb, 1);
        }
        ref_t type = parse_term(ctx, njb);
        if (is_tnil(type)) {
            longjmp(njb, 1);
        }
#endif
        if (!match(ctx, ".")) {
            append_log(ctx, "expected '.'\n");
            longjmp(njb, 1);
        }
        push_bind(ctx, pos);
        ref_t exp = parse_term(ctx, njb);
        if (is_tnil(exp))
            longjmp(njb, 1);
        struct abs *abs = malloc(tsize);
        abs->pos = pos;
        abs->exp = exp;
        pop_bind(ctx);
        return to_ref(abs);
    }
    discard(exp);
    discard(type);
    longjmp(jb, 1);
}

ref_t parse_var(struct ctx *ctx, jmp_buf jb)
{
    char id[lim_id_len];
    skip_spaces(ctx);
    fpos_t pos = save_pos(ctx);
    if (!get_id(ctx, id)) {
        append_log(ctx, "expected identifier\n");
        return tnil;
    }
    debug("%*c%s\n", ctx->len, ' ', __func__);
    int idx = find_bind_idx(ctx, id);
    if (!idx) {
        restore_pos(ctx, pos);
        reset_log(ctx);
        append_log(ctx, "use of undeclared identifier '%s'\n", id);
        longjmp(jb, 1);
    }
    return to_ref(idx);
}

ref_t parse_let(struct ctx *ctx, jmp_buf jb)
{
    char id[lim_id_len];
    if (!match(ctx, "let"))
        return tnil;
    debug("%*c%s\n", ctx->len, ' ', __func__);
    skip_spaces(ctx);
    fpos_t pos = save_pos(ctx);
    if (!get_id(ctx, id)) {
        append_log(ctx, "expected identifier\n");
        longjmp(jb, 1);
    }
    if (!match(ctx, "=")) {
        append_log(ctx, "expected '='\n");
        longjmp(jb, 1);
    }
    ref_t sub = tnil;
    ref_t exp = tnil;
    jmp_buf njb;
    if (!setjmp(njb)) {
        sub = parse_term(ctx, njb);
        if (!sub.raw)
            longjmp(njb, 1);
        if (!match(ctx, "in")) {
            append_log(ctx, "expected 'in'\n");
            longjmp(njb, 1);
        }
        push_bind(ctx, pos);
        exp = parse_term(ctx, njb);
        pop_bind(ctx);
        struct app *app = malloc(tsize);
        struct abs *abs = malloc(tsize);
        abs->exp = exp; 
        abs->pos = pos;
        app->fun = to_ref(abs);
        app->arg = sub;
        return to_ref(app);
    }
    discard(sub);
    discard(exp);
    longjmp(jb, 1);
}

ref_t parse_num(struct ctx *ctx, jmp_buf jb)
{
    int i = match_num(ctx);
    if (i < 0) {
        append_log(ctx, "expected number\n");
        return tnil;
    }
    return to_ref(i);
}

ref_t parse_fun(struct ctx *ctx, jmp_buf jb)
{
    ref_t fun;
    if (match(ctx, "(")) {
        fun = parse_term(ctx, jb);
        if (!match(ctx, ")")) {
            append_log(ctx, "expected ')'\n");
            longjmp(jb, 1);
        }
        goto success;
    }
    fun = parse_let(ctx, jb);
    if (!is_tnil(fun))
        goto success;
    fun = parse_abs(ctx, jb);
    if (!is_tnil(fun))
        goto success;
#if 0
    fun = parse_num(ctx, jb);
    if (!is_tnil(fun))
        goto success;
#endif
    fun = parse_var(ctx, jb);
    if (!is_tnil(fun))
        goto success;
    return tnil;
success:
    reset_log(ctx);
    return fun;
}

ref_t parse_term(struct ctx *ctx, jmp_buf jb)
{
    jmp_buf njb;
    ref_t fun = parse_fun(ctx, jb);
    if (is_tnil(fun))
        longjmp(jb, 1);
    while (!setjmp(njb)) {
        ref_t arg = parse_fun(ctx, njb);
        if (is_tnil(arg)) {
            reset_log(ctx);
            return fun;
        }
        struct app *app = malloc(tsize);
        app->fun = fun;
        app->arg = arg;
        fun = to_ref(app);
    }
    discard(fun);
    longjmp(jb, 1);
}

ref_t parse(struct ctx *ctx, jmp_buf jb)
{
    fpos_t pos = save_pos(ctx);
    fpos_t len = ctx->len;
    ref_t term = parse_term(ctx, jb);
    if (!match_eol(ctx)) {
        append_log(ctx, "unneed character at end of line\n");
        longjmp(jb, 1);
    }
    return term;
}

void print_term(ref_t term, struct ctx *ctx, int lapp);

void print_var(int idx, struct ctx *ctx)
{
    char buf[lim_id_len];
    struct bind *bind = get_bind(ctx, idx);
    fpos_t save = save_pos(ctx);
    restore_pos(ctx, bind->pos);
    if (!get_id(ctx, buf))
        bug();
    emit_str(ctx, buf);
    restore_pos(ctx, save);
}

void print_abs(struct abs *abs, struct ctx *ctx)
{
    char buf[lim_id_len];
    fpos_t save = save_pos(ctx);
    restore_pos(ctx, abs->pos);
    if (!get_id(ctx, buf))
        bug();
    emit_str(ctx, "lambda ");
    emit_str(ctx, buf);
    emit_str(ctx, ".");
    restore_pos(ctx, save);
    push_bind(ctx, abs->pos);
    print_term(abs->exp, ctx, 0);
    pop_bind(ctx);
}

void print_term(ref_t term, struct ctx *ctx, int lapp)
{
    switch (get_tag(term)) {
    case tvar:
        print_var(to_var(term), ctx);
        return;
    case tabs:
        print_abs(to_abs(term), ctx);
        return;
    case tapp:
        {
            struct app *app = to_app(term);
            if (get_tag(app->fun) == tabs) {
                emit_str(ctx, "(");
                print_abs(to_abs(app->fun), ctx);
                emit_str(ctx, ")");
            } else if (get_tag(app->fun) == tvar) {
                print_var(to_var(app->fun), ctx);
            } else {
                print_term(app->fun, ctx, 1);
            }
            emit_str(ctx, " ");
            if (get_tag(app->arg) == tapp || (get_tag(app->arg) == tabs && lapp)) {
                emit_str(ctx, "(");
                print_term(app->arg, ctx, 0);
                emit_str(ctx, ")");
            } else {
                print_term(app->arg, ctx, 0);
            }
        }
        return;
    default:
        bug();
    }
}

void print(struct ctx *ctx, ref_t term)
{
    print_term(term, ctx, 0);
    emit_str(ctx, "\n");
}

ref_t shift(ref_t exp, int d, int c)
{
    switch (get_tag(exp)) {
    case tvar:
        {
            int idx = to_var(exp);
            if (idx > c)
                idx += d;
            return to_ref(idx);
        }
    case tabs:
        {
            struct abs *abs = to_abs(exp);
            abs->exp = shift(abs->exp, d, c+1);
            return to_ref(abs);
        }
    case tapp:
        {
            struct app *app = to_app(exp);
            app->fun = shift(app->fun, d, c);
            app->arg = shift(app->arg, d, c);
            return to_ref(app);
        }
    default:
        bug();
    }
}

ref_t copy(ref_t term)
{
    switch (get_tag(term)) {
    case tvar:
        return term;
    case tabs:
        {
            struct abs *abs = malloc(tsize);
            memcpy(abs, to_abs(term), tsize);
            abs->exp = copy(to_abs(term)->exp);
            return to_ref(abs);
        }
    case tapp:
        {
            struct app *app = malloc(tsize);
            memcpy(app, to_app(term), tsize);
            app->fun = copy(to_app(term)->fun);
            app->arg = copy(to_app(term)->arg);
            return to_ref(app);
        }
    default:
        bug();
    }
}

void discard(ref_t term)
{
    if (is_tnil(term))
        return;
    switch (get_tag(term)) {
    case tvar:
        return;
    case tabs:
        discard(to_abs(term)->exp);
        free(to_abs(term));
        return;
    case tapp:
        discard(to_app(term)->fun);
        discard(to_app(term)->arg);
        free(to_app(term));
        return;
    default:
        bug();
    }
}


ref_t subst(ref_t exp, int j, int c, ref_t sub)
{
    switch (get_tag(exp)) {
    case tvar:
        {
            int idx = to_var(exp);
            if (idx == j+c) {
                sub = copy(sub);
                sub = shift(sub, c, 0);
                return sub;
            }
            return to_ref(idx);
        }
    case tapp:
        {
            struct app *app = to_app(exp);
            app->fun = subst(app->fun, j, c, sub);
            app->arg = subst(app->arg, j, c, sub);
            return to_ref(app);
        }
    case tabs:
        {
            struct abs *abs = to_abs(exp);
            abs->exp = subst(abs->exp, j, c+1, sub);
            return to_ref(abs);
        }
    default:
        bug();
    }
}


int is_val(ref_t term)
{
    return get_tag(term) == tabs;
}

int is_beta_redex(ref_t term)
{
    return get_tag(term) == tapp &&
        get_tag(to_app(term)->fun) == tabs;
}

ref_t beta(ref_t term)
{
    struct app *app = to_app(term);
    struct abs *abs = to_abs(app->fun);
    app->arg = shift(app->arg, 1, 0);
    abs->exp = subst(abs->exp, 1, 0, app->arg);
    term = shift(abs->exp, -1, 0);
    free(abs);
    discard(app->arg);
    free(app);
    return term;
}

int is_delta_redex(struct ctx *ctx, ref_t term)
{
    int idx = to_var(term);
    struct bind *bind = get_bind(ctx, idx);
    return !is_tnil(bind->def);
}

ref_t delta(struct ctx *ctx, ref_t term)
{
    int idx = to_var(term);
    struct bind *bind = get_bind(ctx, idx);
    ref_t sub = copy(bind->def);
    sub = shift(sub, idx, 0);
    return sub;
}

ref_t eval1(struct ctx *ctx, ref_t term, jmp_buf jb)
{
    switch (get_tag(term)) {
    case tvar:
    case tabs:
        debug(" -> [no rule]\n");
        longjmp(jb, 1);
    case tapp:
        {
            struct app *app = to_app(term);
            if (get_tag(app->fun) == tabs && is_val(app->arg)) {
                debug(" -> E-APPABS");
                struct abs *abs = to_abs(app->fun);
                app->arg = shift(app->arg, 1, 0);
                abs->exp = subst(abs->exp, 1, 0, app->arg);
                term = shift(abs->exp, -1, 0);
                free(abs);
                discard(app->arg);
                free(app);
                return term;
            } else if (is_val(app->fun)) {
                debug(" -> E-APP2");
                app->arg = eval1(ctx, app->arg, jb);
                return to_ref(app);
            } else {
                debug(" -> E-APP1");
                app->fun = eval1(ctx, app->fun, jb);
                return to_ref(app);
            }
        }
    default:
        bug();
    }
}

ref_t eval(struct ctx *ctx, ref_t term, jmp_buf jb)
{
    jmp_buf njb;
    while(!setjmp(njb)) {
        if (debug_file) {
            FILE *dst = ctx->dst;
            ctx->dst = debug_file;
            print(ctx, term);
            ctx->dst = dst;
        }
        term = eval1(ctx, term, njb);
        debug("\n");
    }
    return term;
}

int equal(struct ctx *ctx, ref_t pair[2], jmp_buf jb)
{
    int m;
    while (1) {
        /* raw value identity */
        if (pair[0].raw == pair[1].raw)
            return 1;
        enum tag tag0 = get_tag(pair[0]);
        enum tag tag1 = get_tag(pair[1]);
        m = tag0 > tag1;

        if (tag0 == tag1 && tag0 == tabs) {
            push_bind(ctx, to_abs(pair[m])->pos);
            ref_t exps[2] = {to_abs(pair[0])->exp, to_abs(pair[1])->exp};
            int e = equal(ctx, exps, jb);
            to_abs(pair[0])->exp = exps[0];
            to_abs(pair[1])->exp = exps[1];
            pop_bind(ctx);
            return e;
        }

        if (is_delta_redex(ctx, pair[m])) {
            pair[m] = delta(ctx, pair[m]);
            continue;
        }
        if (is_delta_redex(ctx, pair[!m])) {
            pair[!m] = delta(ctx, pair[!m]);
            continue;
        }
        if (is_beta_redex(pair[m])) {
            pair[m] = beta(pair[m]);
            continue;
        }
        if (is_beta_redex(pair[!m])) {
            pair[!m] = beta(pair[!m]);
            continue;
        }
        return 0;
    }
}

void dump_log(struct ctx *ctx)
{
    rewind(ctx->log);
    int c;
    while (1) {
        c = fgetc(ctx->log);
        if (c == EOF)
            break;
        fputc(c, stderr);
    }
}

int main(int argc, char **argv)
{
    for (int i = 1; i < argc; i++) {
        char *opt = argv[i];
        if (*opt == '-')
            while (*++opt)
                switch (*opt) {
                case *"interactive":
                    interactive = 1;
                    break;
                case *"debug":
                    debug_file = stderr;
                    break;
                default:
                    warn("illegal option -- %c\n", *opt);
                }
    }
    struct ctx ctx = {
        .len = 0,
        .src = stdin,
        .dst = stdout,
        .log = tmpfile(),
        .buf = tmpfile(),
        .top = NULL,
    };
    jmp_buf jb;
    if (interactive)
        info("%s", prolog);
    do {
        ref_t term = tnil;
        fpos_t pos = save_pos(&ctx);
        int len = ctx.len;
        if (setjmp(jb)) {
            dump_log(&ctx);
            if (!interactive)
                exit(1);
            restore_pos(&ctx, pos);
            ctx.len = len;
        }
        if (is_eof(ctx.src)) {
            if (interactive)
                info("%s", epilog);
            exit(0);
        }
        debug("read:\n");
        reset_log(&ctx);
        if (interactive)
            info("%s", console);
        read_line(&ctx);
        term = parse(&ctx, jb);
        debug("eval:\n");
        term = eval(&ctx, term, jb);
        debug("print:\n");
        print(&ctx, term);
    } while (interactive);
    return 0;
}
