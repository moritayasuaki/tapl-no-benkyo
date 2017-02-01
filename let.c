#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include <ctype.h>

#define info(...)   fprintf(stderr, __VA_ARGS__)
#define warn(...)   fprintf(stderr, __VA_ARGS__)
#define error(...)  (fprintf(stderr, __VA_ARGS__), exit(1))
#define debug(...)  (debug_file && fprintf(debug_file, __VA_ARGS__))
#define bug()       (error("%s:%d:%s() bug!\n", __FILE__, __LINE__, __func__))
#define lim_id_len  32
FILE *debug_file;
char *interactive;
char *srcname;
union term;
struct bind;
enum tag {tabs, tapp, tvar};

struct ctx {
    int len;
    struct bind *top;
    FILE *log;
    FILE *buf;
    FILE *src;
    FILE *dst;
};

struct bind {
    int pos;
    union term *def;
};

struct var {
    enum tag tag;
    int idx;
    int len;
};

struct abs {
    enum tag tag; fpos_t pos;
    union term *exp;
};

struct app {
    enum tag tag;
    union term *fun;
    union term *arg;
};

union term {
    enum tag tag;
    struct var var;
    struct abs abs;
    struct app app;
};

int iseof(FILE *f)
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
    if (iseof(ctx->buf) && !interactive)
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
    while (1) {
        do {
            c = eat_char(ctx);
        } while (isspace(c));
        if (c != '#') {
            undo_char(ctx, c);
            return;
        }
        do {
           c = eat_char(ctx);
        } while (c != '\n');
    }
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

int match_id(struct ctx *ctx, char *ident)
{
    skip_spaces(ctx);
    fpos_t save = save_pos(ctx);
    if (!match_str(ctx, ident))
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

int is_keyword(char *ident)
{
    return !strcmp(ident, "in") ||
        !strcmp(ident, "lambda") ||
        !strcmp(ident, "let");
}

char *get_id(struct ctx *ctx, char *ident)
{
    skip_spaces(ctx);
    char *p = ident;
    fpos_t save = save_pos(ctx);
    int c = eat_char(ctx);
    if (!(isalpha(c) || c == '_')) {
        undo_char(ctx, c);
        return NULL;
    }
    int l = 0;
    do {
        if (l < lim_id_len - 1)
            ident[l] = c;
        c = eat_char(ctx);
        l++;
    } while (isalnum(c) || c == '_');
    if (l >= lim_id_len) {
        warn("too long identifier\n");
        l = lim_id_len - 1;
    }
    ident[l] = '\0';
    undo_char(ctx, c);
    if (is_keyword(ident)) {
        restore_pos(ctx, save);
        return NULL;
    }
    return ident;
}

int find_bind_idx(struct ctx *ctx, char *ident)
{
    int len = ctx->len;
    struct bind *top = ctx->top;
    fpos_t save = save_pos(ctx);
    int idx;
    for (idx = 0; idx < len; idx++) {
        restore_pos(ctx, top[len-idx-1].pos);
        if (match_id(ctx, ident)) {
            restore_pos(ctx, save);
            return idx;
        }
    }
    restore_pos(ctx, save);
    return idx;
}

struct bind *get_bind(struct ctx *ctx, int idx)
{
    int len = ctx->len;
    struct bind *top = ctx->top;
    if (idx < len)
        return &top[len-idx-1];
    bug();
}

void push_bind(struct ctx *ctx, fpos_t pos)
{
    int len = ctx->len;
    struct bind *top = ctx->top;
    top = realloc(top, (len+1) * sizeof(struct bind));
    top[len].pos = pos;
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

void discard(union term *term);

union term *parse_term(struct ctx *ctx, jmp_buf jb);

#define append_log(ctx, ...) (fprintf((ctx)->log, "%lld:",save_pos(ctx)), fprintf((ctx)->log, __VA_ARGS__), NULL)

void reset_log(struct ctx *ctx) {
    ctx->log = tmpfile();
}

struct abs *parse_abs(struct ctx *ctx, jmp_buf jb)
{
    char buf[lim_id_len];
    if (!match_id(ctx, "lambda")) {
        append_log(ctx, "expected 'lambda'\n");
        return NULL;
    }
    debug("%*c%s\n", ctx->len, ' ', __func__);
    skip_spaces(ctx);
    fpos_t pos = save_pos(ctx);
    if (!get_id(ctx, buf)) {
        append_log(ctx, "expected identifier\n");
        longjmp(jb, 1);
    }
    if (!match_str(ctx, ".")) {
        append_log(ctx, "expected '.'\n");
        longjmp(jb, 1);
    }
    push_bind(ctx, pos);
    union term *exp = parse_term(ctx, jb);
    if (!exp)
        longjmp(jb, 1);
    struct abs *abs = malloc(sizeof(union term));
    abs->tag = tabs;
    abs->pos = pos;
    abs->exp = exp;
    pop_bind(ctx);
    return abs;
}

struct var *parse_var(struct ctx *ctx, jmp_buf jb)
{
    char id[lim_id_len];
    skip_spaces(ctx);
    fpos_t pos = save_pos(ctx);
    if (!get_id(ctx, id)) {
        append_log(ctx, "expected identifier\n");
        return NULL;
    }
    debug("%*c%s\n", ctx->len, ' ', __func__);
    int idx = find_bind_idx(ctx, id);
    if (idx >= ctx->len) {
        restore_pos(ctx, pos);
        reset_log(ctx);
        append_log(ctx, "use of undeclared identifier '%s'\n", id);
        longjmp(jb, 1);
    }
    struct var *var = malloc(sizeof(union term));
    var->tag = tvar;
    var->len = ctx->len;
    var->idx = idx;
    return var;
}

struct app *parse_let(struct ctx *ctx, jmp_buf jb)
{
    char id[lim_id_len];
    if (!match_str(ctx, "let"))
        return NULL;
    skip_spaces(ctx);
    debug("%*c%s\n", ctx->len, ' ', __func__);
    int idx = find_bind_idx(ctx, id);
    fpos_t pos = save_pos(ctx);
    if (!get_id(ctx, id)) {
        append_log(ctx, "expected identifier\n");
        longjmp(jb, 1);
    }
    if (!match_str(ctx, "=")) {
        append_log(ctx, "expected '='\n");
        longjmp(jb, 1);
    }
    union term *sub = NULL;
    union term *exp = NULL;
    jmp_buf njb;
    if (!setjmp(njb)) {
        sub = parse_term(ctx, njb);
        if (!sub)
            longjmp(njb, 1);
        if (!match_str(ctx, "in")) {
            append_log(ctx, "expected 'in'\n");
            longjmp(njb, 1);
        }
        push_bind(ctx, pos);
        exp = parse_term(ctx, njb);
        pop_bind(ctx);
        struct app *app = malloc(sizeof(union term));
        struct abs *abs = malloc(sizeof(union term));
        abs->tag = tabs;
        abs->exp = (union term *)exp; 
        abs->pos = pos;
        app->tag = tapp;
        app->fun = (union term *)abs;
        app->arg = sub;
        return app;
    }
    discard(sub);
    discard(exp);
    longjmp(jb, 1);
}
union term *parse_fun(struct ctx *ctx, jmp_buf jb)
{
    union term *fun;
    if (match_str(ctx, "(")) {
        fun = parse_term(ctx, jb);
        if (!match_str(ctx, ")")) {
            append_log(ctx, "expected ')'\n");
            longjmp(jb, 1);
        }
        goto success;
    }
    fun = (union term *)parse_let(ctx, jb);
    if (fun)
        goto success;
    fun = (union term *)parse_abs(ctx, jb);
    if (fun)
        goto success;
    fun = (union term *)parse_var(ctx, jb);
    if (fun)
        goto success;
    return NULL;
success:
    reset_log(ctx);
    return fun;
}

union term *parse_term(struct ctx *ctx, jmp_buf jb)
{
    jmp_buf njb;
    union term *fun = parse_fun(ctx, jb);
    if (!fun)
        longjmp(jb, 1);
    while (!setjmp(njb)) {
        union term *arg = parse_fun(ctx, njb);
        if (!arg) {
            reset_log(ctx);
            return fun;
        }
        struct app *app = malloc(sizeof(union term));
        app->tag = tapp;
        app->fun = fun;
        app->arg = arg;
        fun = (union term *)app;
    }
    discard(fun);
    longjmp(jb, 1);
}

union term *parse(struct ctx *ctx, jmp_buf jb)
{
    fpos_t pos = save_pos(ctx);
    fpos_t len = ctx->len;
    union term *term = parse_term(ctx, jb);
    if (!match_eol(ctx)) {
        append_log(ctx, "unneed character at end of line\n");
        longjmp(jb, 1);
    }
    return term;
}

void print_term(union term *term, struct ctx *ctx, int lapp);

void print_var(struct var *var, struct ctx *ctx)
{
    char buf[lim_id_len];
    struct bind *bind = get_bind(ctx, var->idx);
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

void print_fun(union term *fun, struct ctx *ctx)
{
    switch (fun->tag) {
    case tabs:
        print_abs(&fun->abs, ctx);
        return;
    case tvar:
        print_var(&fun->var, ctx);
        return;
    default:
        bug();
    }
}

void print_term(union term *term, struct ctx *ctx, int lapp)
{
    if (term->tag == tapp) {
        struct app *app = &term->app;
        if (app->fun->tag == tabs) {
            emit_str(ctx, "(");
            print_fun(app->fun, ctx);
            emit_str(ctx, ")");
        } else if (app->fun->tag == tvar) {
            print_fun(app->fun, ctx);
        } else {
            print_term(app->fun, ctx, 1);
        }
        emit_str(ctx, " ");
        if (app->arg->tag == tapp || (app->arg->tag == tabs && lapp)) {
            emit_str(ctx, "(");
            print_term(app->arg, ctx, 0);
            emit_str(ctx, ")");
        } else {
            print_term(app->arg, ctx, 0);
        }
    } else {
        print_fun(term, ctx);
    }
}

void print(struct ctx *ctx, union term *term)
{
    print_term(term, ctx, 0);
    emit_str(ctx, "\n");
}

union term *shift(union term *exp, int d, int c)
{
    switch (exp->tag) {
    case tapp:
        exp->app.fun = shift(exp->app.fun, d, c);
        exp->app.arg = shift(exp->app.arg, d, c);
        return exp;
    case tabs:
        exp->abs.exp = shift(exp->abs.exp, d, c+1);
        return exp;
    case tvar:
        if (exp->var.idx >= c)
            exp->var.idx += d;
        return exp;
    default:
        bug();
    }
}

union term *copy(union term *term)
{
    union term *new = malloc(sizeof(union term));
    memcpy(new, term, sizeof(union term));
    switch (term->tag) {
    case tapp:
        new->app.fun = copy(term->app.fun);
        new->app.arg = copy(term->app.arg);
        return new;
    case tabs:
        new->abs.exp = copy(term->abs.exp);
        return new;
    case tvar:
        return new;
    default:
        bug();
    }
}

void discard(union term *term)
{
    if (!term)
        return;
    switch (term->tag) {
    case tapp:
        discard(term->app.fun);
        discard(term->app.arg);
        free(term);
        return;
    case tabs:
        discard(term->abs.exp);
        free(term);
        return;
    case tvar:
        free(term);
        return;
    default:
        bug();
    }
}

union term *subst(union term *exp, int j, int c, union term *sub)
{
    switch (exp->tag) {
    case tapp:
        exp->app.fun = subst(exp->app.fun, j, c, sub);
        exp->app.arg = subst(exp->app.arg, j, c, sub);
        return exp;
    case tabs:
        exp->abs.exp = subst(exp->abs.exp, j, c+1, sub);
        return exp;
    case tvar:
        if (exp->var.idx == j+c) {
            union term *new = copy(sub);
            free(exp);
            return shift(new, c, 0);
        }
        return exp;
    default:
        bug();
    }
}

union term *subst1(union term *t, union term *s)
{
    s = shift(s, 1, 0);
    t = subst(t, 0, 0, s);
    t = shift(t, -1, 0);
    return t;
}

int is_val(union term *term)
{
    return term->tag == tabs;
}

int is_beta_radix(union term *term)
{
    return term->tag == tapp && term->app.fun->tag == tabs;
}

union term *eval1(struct ctx *ctx, union term *term, jmp_buf jb)
{
    switch (term->tag) {
    case tapp:
        {
            struct app *app = &term->app;
            if (app->fun->tag == tabs && is_val(app->arg)) {
                debug(" -> E-APPABS");
                term = subst1(app->fun->abs.exp, app->arg);
                free(app->fun);
                discard(app->arg);
                free(app);
                return term;
            } else if (is_val(app->fun)) {
                debug(" -> E-APP2");
                app->arg = eval1(ctx, app->arg, jb);
                return term;
            } else {
                debug(" -> E-APP1");
                app->fun = eval1(ctx, app->fun, jb);
                return term;
            }
        }
    case tabs:
    case tvar:
        debug(" -> [no rule]\n");
        longjmp(jb, 1);
    default:
        bug();
    }
}

union term *eval(struct ctx *ctx, union term *term, jmp_buf jb)
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

struct ctx ctx;

int main(int argc, char **argv)
{
    jmp_buf jb;
    for (int i = 1; i < argc; i++) {
        char *opt = argv[i];
        if (opt[0] == '-')
            switch (opt[1]) {
            case 'f':
                srcname = argv[++i];
                break;
            default:
                for (int j = 1; opt[j]; j++)
                    switch (opt[j]) {
                    case 'i':
                        interactive = ">>> ";
                        break;
                    case 'd':
                        debug_file = stderr;
                        break;
                    default:
                        warn("illegal option -- %c", *opt);
                    }
            }
    }
    ctx.len = 0;
    ctx.src = srcname?fopen(srcname,"r"):stdin;
    ctx.dst = stdout;
    ctx.log = tmpfile();
    ctx.buf = tmpfile();
    ctx.top = NULL;
loop:
    debug("loop :\n");
    union term *term;
    fpos_t pos = save_pos(&ctx);
    int len = ctx.len;
    if (setjmp(jb)) {
        dump_log(&ctx);
        if (!interactive)
            return 1;
        restore_pos(&ctx, pos);
        ctx.len = len;
    }
    if (iseof(ctx.src))
        return 1;
    if (interactive)
        info("%s", interactive);
    debug("read :\n");
    reset_log(&ctx);
    read_line(&ctx);
    term = parse(&ctx, jb);
    debug("eval :\n");
    term = eval(&ctx, term, jb);
    debug("print :\n");
    print(&ctx, term);
    if (interactive && !iseof(ctx.src))
        goto loop;
    return 0;
}
