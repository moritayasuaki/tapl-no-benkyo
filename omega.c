#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <setjmp.h>
#include <ctype.h>
#include <assert.h>
#include <stdalign.h>
#include <limits.h>
#include <stddef.h>

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
fpos_t name = -4;

typedef struct {intptr_t raw;} ref_t;
typedef struct {jmp_buf jb;} frm_t;

struct ctx {
    int len;
    struct bind *top;
    FILE *log;
    FILE *buf;
    FILE *src;
    FILE *dst;
    frm_t frm;
};

struct bind {
    ref_t type;
    ref_t def;
    fpos_t pos;
};

struct abs {
    ref_t type;
    ref_t exp;
    fpos_t pos;
};

struct app {
    ref_t fun;
    ref_t arg;
    fpos_t pos;
};

struct arr {
    ref_t src;
    ref_t dst;
    fpos_t pos;
};

struct val {
    int vtag;
};

union term {
    max_align_t align;
    struct abs abs;
    struct app app;
    struct arr arr;
    struct val val;
};

enum tag {
    tabs,
    tapp,
    tarr,
    tval,

    tvar,
    tuniv,
    tnil,
};

#define is_nil(x) (((x).raw) == 0)
#define nil (ref_t){0}
#define univ (ref_t){1}
#define is_univ(x) (((x).raw) == 1)
#define tsize  sizeof(union term)
#define talign alignof(union term)
static_assert(tval < talign, "num of reference tag exceed pointer align\n");

int to_int(ref_t ref)
{
    return ref.raw;
}
#define to_var(x) to_int(x)

void *to_ptr(ref_t ref)
{
    return (void *)(ref.raw & -talign);
}

#define to_abs(x) ((struct abs *)to_ptr(x))
#define to_app(x) ((struct app *)to_ptr(x))
#define to_arr(x) ((struct arr *)to_ptr(x))

#define to_ref(x) generic((x),\
    struct abs*:    (ref_t){(intptr_t)(x) | tabs},\
    struct app*:    (ref_t){(intptr_t)(x) | tapp},\
    struct arr*:    (ref_t){(intptr_t)(x) | tarr},\
    struct val*:    (ref_t){(intptr_t)(x) | tval},\
    int:            (ref_t){(intptr_t)(x)},\
    default: nil)

enum tag get_tag(ref_t ref)
{
    if (is_nil(ref))
        return tnil;
    if (is_univ(ref))
        return tuniv;
    if (min_idx <= ref.raw && ref.raw < 0)
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

int read_num(struct ctx *ctx)
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
        !strcmp(id, "let") ||
        !strcmp(id, "int");
}

struct bind *get_base(struct ctx *ctx)
{
    return ctx->top + ctx->len;
}

fpos_t read_id(struct ctx *ctx, char *id)
{
    skip_spaces(ctx);
    char *p = id;
    fpos_t pos = save_pos(ctx);
    int c = eat_char(ctx);
    if (!(isalpha(c) || c == '_')) {
        undo_char(ctx, c);
        return EOF;
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
        restore_pos(ctx, pos);
        return EOF;
    }
    return pos;
}

int find_bind_idx(struct ctx *ctx, char *id)
{
    int len = ctx->len;
    struct bind *base = get_base(ctx);
    fpos_t save = save_pos(ctx);
    for (int idx=-1; idx >= -len; idx--) {
        restore_pos(ctx, base[idx].pos);
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
    if (0 > idx && idx >= -len)
        return &base[idx];
    bug();
}

void push_bind(struct ctx *ctx, fpos_t pos, ref_t type, ref_t def)
{
    int len = ctx->len;
    struct bind *top = ctx->top;
    top = realloc(top, (len+1) * sizeof(struct bind));
    top[len].pos = pos;
    top[len].type = type;
    top[len].def = def;
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
ref_t parse_type(struct ctx *ctx, jmp_buf jb);
ref_t parse_var(struct ctx *ctx, jmp_buf jb);

#define parse_log(ctx, ...) (fprintf((ctx)->log, "%lld:",save_pos(ctx)), fprintf((ctx)->log, __VA_ARGS__))

void reset_log(struct ctx *ctx)
{
    ctx->log = tmpfile();
}

ref_t parse_all(struct ctx *ctx, jmp_buf jb)
{
    char id[lim_id_len];
    jmp_buf njb;
    ref_t src = nil;
    ref_t dst = nil;
    if (!match(ctx, "forall"))
        return nil;
    if (!setjmp(njb)) {
        debug("%*c%s\n", ctx->len, ' ', __func__);
        fpos_t pos = read_id(ctx, id);
        if (pos == EOF) {
            parse_log(ctx, "expected identifier\n");
            longjmp(njb, 1);
        }
        src = univ;
        if (!match(ctx, ".")) {
            parse_log(ctx, "expected '.'\n");
            longjmp(njb, 1);
        }
        push_bind(ctx, pos, src, nil);
        dst = parse_type(ctx, njb);
        pop_bind(ctx);
        struct arr *arr = malloc(tsize);
        arr->src = src;
        arr->dst = dst;
        arr->pos = pos;
        return to_ref(arr);
    }
    discard(src);
    discard(dst);
    longjmp(jb, 1);
}

ref_t parse_type1(struct ctx *ctx, jmp_buf jb)
{
    ref_t type;
    if (match(ctx, "(")) {
        type = parse_type(ctx, jb);
        if (!match(ctx, ")")) {
            parse_log(ctx, "exptected ')'\n");
            longjmp(jb, 1);
        }
        return type;
    }
    type = parse_all(ctx, jb);
    if (!is_nil(type))
        return type;
    type = parse_var(ctx, jb);
    if (!is_nil(type))
        return type;
    return nil;
}

ref_t parse_type(struct ctx *ctx, jmp_buf jb)
{
    ref_t type = parse_type1(ctx, jb);
    if (is_nil(type))
        longjmp(jb, 1);
    if (!match(ctx, "->"))
        return type;
    push_bind(ctx, EOF, type, nil);
    ref_t dst = parse_type(ctx, jb);
    pop_bind(ctx);
    if (is_nil(dst)) {
        discard(type);
        longjmp(jb, 1);
    }
    struct arr *arr = malloc(tsize);
    arr->src = type;
    arr->dst = dst;
    arr->pos = EOF;
    return to_ref(arr);
}

ref_t parse_anot(struct ctx *ctx, jmp_buf jb)
{
    if (!match(ctx, ":")) {
        parse_log(ctx, "expected ':'\n");
        return nil;
    }
    ref_t src = parse_type(ctx, jb);
    return src;
}

ref_t parse_abs(struct ctx *ctx, jmp_buf jb)
{
    char buf[lim_id_len];
    jmp_buf njb;
    ref_t type = nil;
    ref_t exp = nil;
    if (!match(ctx, "lambda")) {
        parse_log(ctx, "expected 'lambda'\n");
        return nil;
    }
    if (!setjmp(njb)) {
        debug("%*c%s\n", ctx->len, ' ', __func__);
        fpos_t pos = read_id(ctx, buf);
        if (pos == EOF) {
            parse_log(ctx, "expected identifier\n");
            longjmp(njb, 1);
        }
        type = parse_anot(ctx, njb);
        if (is_nil(type))
            type = univ;
        if (!match(ctx, ".")) {
            parse_log(ctx, "expected '.'\n");
            longjmp(njb, 1);
        }
        push_bind(ctx, pos, type, nil);
        exp = parse_term(ctx, njb);
        if (is_nil(exp))
            longjmp(njb, 1);
        struct abs *abs = malloc(tsize);
        abs->pos = pos;
        abs->exp = exp;
        abs->type = type;
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
    fpos_t pos = read_id(ctx, id);
    if (pos == EOF) {
        parse_log(ctx, "expected identifier\n");
        return nil;
    }
    debug("%*c%s\n", ctx->len, ' ', __func__);
    int idx = find_bind_idx(ctx, id);
    if (!idx) {
        restore_pos(ctx, pos);
        reset_log(ctx);
        parse_log(ctx, "use of undeclared identifier '%s'\n", id);
        longjmp(jb, 1);
    }
    return to_ref(idx);
}

ref_t parse_let(struct ctx *ctx, jmp_buf jb)
{
    char id[lim_id_len];
    ref_t type = nil;
    ref_t sub = nil;
    ref_t exp = nil;
    jmp_buf njb;
    if (!match(ctx, "let"))
        return nil;
    if (!setjmp(njb)) {
        debug("%*c%s\n", ctx->len, ' ', __func__);
        skip_spaces(ctx);
        fpos_t pos = read_id(ctx, id);
        if (pos == EOF) {
            parse_log(ctx, "expected identifier\n");
            longjmp(njb, 1);
        }
        parse_anot(ctx, njb);
        if (!match(ctx, "=")) {
            parse_log(ctx, "expected '='\n");
            longjmp(njb, 1);
        }
        sub = parse_term(ctx, njb);
        if (!sub.raw)
            longjmp(njb, 1);
        if (!match(ctx, "in")) {
            parse_log(ctx, "expected 'in'\n");
            longjmp(njb, 1);
        }
        push_bind(ctx, pos, type, nil);
        exp = parse_term(ctx, njb);
        pop_bind(ctx);
        struct app *app = malloc(tsize);
        struct abs *abs = malloc(tsize);
        abs->type = type;
        abs->exp = exp; 
        abs->pos = pos;
        app->fun = to_ref(abs);
        app->arg = sub;
        app->pos = pos;
        return to_ref(app);
    }
    discard(type);
    discard(sub);
    discard(exp);
    longjmp(jb, 1);
}

ref_t parse_num(struct ctx *ctx, jmp_buf jb);

ref_t parse_num(struct ctx *ctx, jmp_buf jb)
{
    fpos_t save = save_pos(ctx);
    int num = read_num(ctx);
    if (num < 0) {
        parse_log(ctx, "expected number\n");
        restore_pos(ctx, save);
        return nil;
    }
    return to_ref(num);
}

ref_t parse_fun(struct ctx *ctx, jmp_buf jb)
{
    ref_t fun;
    if (match(ctx, "(")) {
        fun = parse_term(ctx, jb);
        if (!match(ctx, ")")) {
            parse_log(ctx, "expected ')'\n");
            longjmp(jb, 1);
        }
        goto success;
    }
    fun = parse_let(ctx, jb);
    if (!is_nil(fun))
        goto success;
    fun = parse_abs(ctx, jb);
    if (!is_nil(fun))
        goto success;
    fun = parse_num(ctx, jb);
    if (!is_nil(fun))
        goto success;
    fun = parse_var(ctx, jb);
    if (!is_nil(fun))
        goto success;
    return nil;
success:
    reset_log(ctx);
    return fun;
}

ref_t parse_term(struct ctx *ctx, jmp_buf jb)
{
    jmp_buf njb;
    ref_t fun = parse_fun(ctx, jb);
    if (is_nil(fun))
        longjmp(jb, 1);
    fpos_t pos = save_pos(ctx);
    while (!setjmp(njb)) {
        ref_t arg = parse_fun(ctx, njb);
        if (is_nil(arg)) {
            reset_log(ctx);
            return fun;
        }
        struct app *app = malloc(tsize);
        app->fun = fun;
        app->arg = arg;
        app->pos = pos;
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
        parse_log(ctx, "unneed character at end of line\n");
        longjmp(jb, 1);
    }
    return term;
}

void print_term(ref_t term, struct ctx *ctx, int lapp);

void emit_id(struct ctx *ctx, fpos_t pos)
{
    char buf[lim_id_len];
    if (pos < 0) {
        buf[0] = '_';
        buf[1] = (-pos) % ('z' - 'a' + 1) + 'a';
        buf[2] = '\0';
    } else {
        fpos_t save = save_pos(ctx);
        restore_pos(ctx, pos);
        if (read_id(ctx, buf) == EOF)
            bug();
        restore_pos(ctx, save);
    }
    emit_str(ctx, buf);
}

void print_var(int idx, struct ctx *ctx)
{
    struct bind *bind = get_bind(ctx, idx);
    emit_id(ctx, bind->pos);
}

void print_abs(struct abs *abs, struct ctx *ctx)
{
    emit_str(ctx, "lambda ");
    emit_id(ctx, abs->pos);
    if (!is_univ(abs->type)) {
        emit_str(ctx, ":");
        print_term(abs->type, ctx, 1);
    }
    emit_str(ctx, ".");
    push_bind(ctx, abs->pos, abs->type, nil);
    print_term(abs->exp, ctx, 0);
    pop_bind(ctx);
}

void print_all(ref_t term, struct ctx *ctx) {
    struct arr *arr = to_arr(term);
    emit_str(ctx, "forall ");
    emit_id(ctx, arr->pos);
    emit_str(ctx, ".");
    push_bind(ctx, arr->pos, univ, nil);
    print_term(arr->dst, ctx, 0);
    pop_bind(ctx);
}

void print_arr(ref_t term, struct ctx *ctx) {
    struct arr *arr = to_arr(term);
    if (get_tag(arr->src) == tarr) {
        emit_str(ctx, "(");
        print_term(arr->src, ctx, 0);
        emit_str(ctx, ")");
    } else {
        print_term(arr->src, ctx, 0);
    }
    emit_str(ctx, "->");
    push_bind(ctx, arr->pos, arr->src, nil);
    print_term(arr->dst, ctx, 0);
    pop_bind(ctx);
}

void print_term(ref_t term, struct ctx *ctx, int lapp)
{
    switch (get_tag(term)) {
        struct app *app;
    case tvar:
        print_var(to_var(term), ctx);
        return;
    case tabs:
        print_abs(to_abs(term), ctx);
        return;
    case tapp:
        app = to_app(term);
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
        return;
    case tarr:
        if (get_tag(to_arr(term)->src) == tuniv)
            print_all(term, ctx);
        else
            print_arr(term, ctx);
        return;
    case tuniv:
        emit_str(ctx, "*");
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
        int idx;
        struct abs *abs;
        struct app *app;
        struct arr *arr;
    case tvar:
        idx = to_var(exp);
        if (idx < c)
            idx += d;
        return to_ref(idx);
    case tabs:
        abs = to_abs(exp);
        abs->type = shift(abs->type, d, c);
        abs->exp = shift(abs->exp, d, c-1);
        return to_ref(abs);
    case tapp:
        app = to_app(exp);
        app->fun = shift(app->fun, d, c);
        app->arg = shift(app->arg, d, c);
        return to_ref(app);
    case tarr:
        arr = to_arr(exp);
        arr->src = shift(arr->src, d, c);
        arr->dst = shift(arr->dst, d, c-1);
        return to_ref(arr);
    case tuniv:
        return exp;
    default:
        bug();
    }
}

ref_t copy(ref_t term)
{
    switch (get_tag(term)) {
        struct abs *abs;
        struct app *app;
        struct arr *arr;
    case tvar:
        return term;
    case tabs:
        abs = malloc(tsize);
        memcpy(abs, to_abs(term), tsize);
        abs->exp = copy(to_abs(term)->exp);
        abs->type = copy(to_abs(term)->type);
        return to_ref(abs);
    case tapp:
        app = malloc(tsize);
        memcpy(app, to_app(term), tsize);
        app->fun = copy(to_app(term)->fun);
        app->arg = copy(to_app(term)->arg);
        return to_ref(app);
    case tarr:
        arr = malloc(tsize);
        memcpy(arr, to_arr(term), tsize);
        arr->src = copy(to_arr(term)->src);
        arr->dst = copy(to_arr(term)->dst);
        return to_ref(arr);
    case tuniv:
        return term;
    default:
        bug();
    }
}

void discard(ref_t term)
{
    if (is_nil(term))
        return;
    switch (get_tag(term)) {
    case tvar:
        return;
    case tabs:
        discard(to_abs(term)->exp);
        discard(to_abs(term)->type);
        free(to_abs(term));
        return;
    case tapp:
        discard(to_app(term)->fun);
        discard(to_app(term)->arg);
        free(to_app(term));
        return;
    case tarr:
        discard(to_arr(term)->src);
        discard(to_arr(term)->dst);
        free(to_arr(term));
        return;
    case tuniv:
        return;
    default:
        bug();
    }
}

ref_t subst(ref_t exp, int j, int c, ref_t sub)
{
    switch (get_tag(exp)) {
        int idx;
        struct app *app;
        struct abs *abs;
        struct arr *arr;
    case tvar:
        idx = to_var(exp);
        if (idx == j+c) {
            sub = copy(sub);
            sub = shift(sub, c, 0);
            return sub;
        }
        return to_ref(idx);
    case tapp:
        app = to_app(exp);
        app->fun = subst(app->fun, j, c, sub);
        app->arg = subst(app->arg, j, c, sub);
        return to_ref(app);
    case tabs:
        abs = to_abs(exp);
        abs->type = subst(abs->type, j, c, sub);
        abs->exp = subst(abs->exp, j, c-1, sub);
        return to_ref(abs);
    case tarr:
        arr = to_arr(exp);
        arr->src = subst(arr->src, j, c, sub);
        arr->dst = subst(arr->dst, j, c-1, sub);
        return to_ref(arr);
    case tuniv:
        return exp;
    default:
        bug();
    }
}

int is_beta_redex(struct ctx *ctx, ref_t term)
{
    return get_tag(term) == tapp &&
        get_tag(to_app(term)->fun) == tabs;
}

ref_t beta_reduce(struct ctx *ctx, ref_t term)
{
    struct app *app = to_app(term);
    struct abs *abs = to_abs(app->fun);
    app->arg = shift(app->arg, -1, 0);
    abs->exp = subst(abs->exp, -1, 0, app->arg);
    term = shift(abs->exp, 1, 0);
    free(abs);
    discard(app->arg);
    free(app);
    return term;
}

int is_delta_redex(struct ctx *ctx, ref_t term)
{
    return get_tag(term) == tvar &&
        !is_nil(get_bind(ctx, to_var(term))->def);
}

ref_t delta_reduce(struct ctx *ctx, ref_t term)
{
    int idx = to_var(term);
    struct bind *bind = get_bind(ctx, idx);
    ref_t sub = copy(bind->def);
    sub = shift(sub, idx, 0);
    return sub;
}

int is_val(struct ctx *ctx, ref_t term)
{
    return get_tag(term) == tabs;
}

int have_weak_head_redex(struct ctx *ctx, ref_t term)
{
    return is_delta_redex(ctx, term) || is_beta_redex(ctx, term);
}

int have_head_redex(struct ctx *ctx, ref_t term)
{
    int ret;
    if (have_weak_head_redex(ctx, term))
        return 1;
    switch (get_tag(term)) {
    case tvar:
    case tapp:
        return 0;
    case tabs:
        push_bind(ctx, to_abs(term)->pos, to_abs(term)->type, nil);
        ret = have_head_redex(ctx, term);
        pop_bind(ctx);
        return ret;
    default:
        bug();
    }
}

int have_redex(struct ctx *ctx, ref_t term)
{
    int ret;
    if (have_weak_head_redex(ctx, term))
        return 1;
    switch (get_tag(term)) {
    case tvar:
        return 0;
    case tabs:
        push_bind(ctx, to_abs(term)->pos, to_abs(term)->type, nil);
        ret = have_redex(ctx, to_abs(term)->exp);
        pop_bind(ctx);
        return ret;
    case tapp:
        return have_redex(ctx, to_app(term)->fun) &&
            have_redex(ctx, to_app(term)->arg);
    default:
        bug();
    }
}

#define type_log(ctx, pos, ...) (fprintf((ctx)->log, "%lld:", pos), fprintf((ctx->log), __VA_ARGS__ ))

int compare_type(struct ctx *ctx, ref_t t0, ref_t t1, jmp_buf jb)
{
    if (t0.raw == t1.raw)
        return 0;
    enum tag tag[2];
    tag[0] = get_tag(t0);
    tag[1] = get_tag(t1);
    for (int i = 0; i < 2; i++) {
        if (tag[i] == tabs) {
            type_log(ctx, to_abs(t0)->pos,  "lambda abstraction is not allowed in type context\n");
            longjmp(jb, 1);
        }
        if (tag[i] == tapp) {
            type_log(ctx, to_abs(t0)->pos,  "application is not allowed in type context\n");
            longjmp(jb, 1);
        }
    }
    if (tag[0] != tag[1])
        return 1;
    switch (tag[0]) {
        struct arr *arr0;
        struct arr *arr1;
    case tvar:
        return 1;
    case tuniv:
        return 1;
    case tarr:
        arr0 = to_arr(t0);
        arr1 = to_arr(t1);
        return compare_type(ctx, arr0->src, arr1->src, jb) &&
            compare_type(ctx, arr0->dst, arr1->dst, jb);
    default:
        bug();
    }
}

ref_t check_type(struct ctx *ctx, ref_t term, jmp_buf jb)
{
    switch (get_tag(term)) {
        struct app *app;
        struct abs *abs;
    case tvar:
        return get_bind(ctx, to_var(term))->type;
    case tabs:
        {
            abs = to_abs(term);
            ref_t src = abs->type;
            push_bind(ctx, abs->pos, src, nil);
            ref_t dst = check_type(ctx, abs->exp, jb);
            if (is_nil(dst)) {
                type_log(ctx, abs->pos, "typing expression in abstraction failed\n");
                return nil;
            }
            pop_bind(ctx);
            struct arr *arr = malloc(tsize);
            arr->src = src;
            arr->dst = dst;
            if (is_univ(src))
                arr->pos = abs->pos;
            return to_ref(arr);
        }
    case tapp:
        app = to_app(term);
        ref_t funtype = check_type(ctx, app->fun, jb);
        if (is_nil(funtype)) {
            type_log(ctx, app->pos, "typing function failed\n");
            return nil;
        }
        ref_t src = check_type(ctx, app->arg, jb);
        if (is_nil(src))
            return nil;
        if (get_tag(funtype) == tarr) {
            struct arr *arr = to_arr(funtype);
            if (compare_type(ctx, arr->src, src, jb) == 0)
                return arr->dst;
            type_log(ctx, app->pos,  "parameter type mismatch\n");
        } else {
            type_log(ctx, app->pos, "arrow type expected\n");
        }
        longjmp(jb, 1);
    default:
        bug();
    }
}

enum eval_red {
    eval_beta    = 1<<0,
    eval_delta   = 1<<1,
};

enum eval_order {
    eval_cbv,
    eval_cvn,
};

enum eval_goal {
    eval_weak_head_normal,
    eval_head_normal,
    eval_normal,
};

ref_t eval1(struct ctx *ctx, ref_t term, jmp_buf jb)
{
    switch (get_tag(term)) {
        struct app *app;
    case tvar:
        if (is_delta_redex(ctx, term)) {
            debug(" -> E-DELTA");
            term = delta_reduce(ctx, term);
            return term;
        }
    case tabs:
        debug(" -> [no rule]\n");
        longjmp(jb, 1);
    case tapp:
        app = to_app(term);
        if (is_beta_redex(ctx, term) && is_val(ctx, app->arg)) {
            struct abs *abs = to_abs(app->fun);
            if (is_univ(abs->type)) {
                debug(" -> E-TBETA");
                term = beta_reduce(ctx, term);
            } else {
                debug(" -> E-BETA");
                term = beta_reduce(ctx, term);
            }
            return term;
        } else if (is_val(ctx, app->fun)){
            debug(" -> E->APP2");
            app->arg = eval1(ctx, app->arg, jb);
            return to_ref(app);
        } else {
            debug(" -> E-APP1");
            app->fun = eval1(ctx, app->fun, jb);
            return to_ref(app);
        }
        debug(" -> [no rule]\n");
        longjmp(jb, 1);
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
        ref_t term = nil;
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
        debug("check:\n");
        ref_t type = check_type(&ctx, term, jb);
        print(&ctx, type);
        debug("eval:\n");
        term = eval(&ctx, term, jb);
        debug("print:\n");
        print(&ctx, term);
    } while (interactive);
    return 0;
}
