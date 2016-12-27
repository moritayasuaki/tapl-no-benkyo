#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include <ctype.h>

FILE *dbg;
#define error(...) (fprintf(stderr, __VA_ARGS__), exit(1))
#define debug(...) (dbg && fprintf(dbg, __VA_ARGS__))

union term;
enum tag {tabs, tapp, tvar};

struct ctx {
    fpos_t pos;
    int len;
    void *binding;
    struct ctx *next;
};

struct var {
    enum tag tag;
    int idx;
    int len;
};

struct abs {
    enum tag tag;
    fpos_t pos;
    union term *exp;
};

struct app {
    enum tag tag;
    union term *fun;
    union term *arg;
    struct app *next;
};

union term {
    enum tag tag;
    struct var v;
    struct abs ab;
    struct app ap;
};

void skip_spaces(FILE *src) {
    int c;
    do {
        c = fgetc(src);
    } while (isspace(c));
    ungetc(c, src);
}

int match_str(FILE *src, char *str)
{
    fpos_t save;
    fgetpos(src, &save);
    while (*str)
        if (fgetc(src) != *str++)
            goto mismatch;
    return 1;
mismatch:
    fsetpos(src, &save);
    return 0;
}

int match_id(FILE *src, char *id)
{
    int c;
    fpos_t save;
    fgetpos(src, &save);
    if (!match_str(src, id))
        goto mismatch;
    c = fgetc(src);
    if (isalnum(c) || c == '_')
        goto mismatch;
    return 1;
mismatch:
    fsetpos(src, &save);
    return 0;
}

char *get_id(FILE *src, char *id)
{
    int c;
    char *p = id;
    c = fgetc(src);
    if (!(isalpha(c) || c == '_')) {
        ungetc(c, src);
        return NULL;
    }
    do {
        *p++ = c;
        c = fgetc(src);
    } while (p - id < 32 && (isalnum(c) || c == '_'));
    ungetc(c, src);
    *p = '\0';
    return id;
}

union term *parse_term(FILE *src, struct ctx *ctx);

struct ctx *find_ctx(struct ctx *ctx, FILE *src, char *id)
{
    if (ctx->next == ctx)
        return NULL;
    fsetpos(src, &ctx->pos);
    if (match_id(src, id))
        return ctx;
    return find_ctx(ctx->next, src, id);
}

struct ctx *push_ctx(struct ctx *ctx, fpos_t pos) {
    struct ctx *top = malloc(sizeof(struct ctx));
    top->pos = pos;
    top->next = ctx;
    top->len = ctx->len + 1;
    return top;
}

struct ctx *pop_ctx(struct ctx *ctx)
{
    struct ctx *next = ctx->next;
    free(ctx);
    return next;
}

struct abs *parse_abs(FILE *src, struct ctx *ctx)
{
    char buf[32];
    skip_spaces(src);
    if (!match_id(src, "lambda"))
        return NULL;
    skip_spaces(src);
    fpos_t p;
    fgetpos(src, &p);
    if (!get_id(src, buf))
        error("invalid identifier");
    skip_spaces(src);
    if (!match_str(src, "."))
        error(". is expected\n");
    ctx = push_ctx(ctx, p);
    union term *e = parse_term(src, ctx);
    if (!e)
        error("parse error\n");
    struct abs *ab = malloc(sizeof(union term));
    ab->tag = tabs;
    ab->pos = p;
    ab->exp = e;
    ctx = pop_ctx(ctx);
    return ab;
}

struct var *parse_var(FILE *src, struct ctx *ctx)
{
    char buf[32];
    int idx;
    fpos_t save;
    skip_spaces(src);
    if (!get_id(src, buf))
        return NULL;
    fgetpos(src, &save);
    struct ctx *hit = find_ctx(ctx, src, buf);
    fsetpos(src, &save);
    if (!hit)
        error("undefined identifier %s\n", buf);
    struct var *v = malloc(sizeof(union term));
    v->tag = tvar;
    v->len = ctx->len;
    v->idx = ctx->len - hit->len;
    return v;
}

union term *parse_fun(FILE *src, struct ctx *ctx)
{
    union term *f;
    skip_spaces(src);
    if (match_str(src, "(")) {
        skip_spaces(src);
        f = parse_term(src, ctx);
        if (!match_str(src, ")"))
            error("unmatched paren\n");
        return f;
    }
    f = (union term *)parse_abs(src, ctx);
    if (f)
        return f;
    return (union term *)parse_var(src, ctx);
}

union term *parse_term(FILE *src, struct ctx *ctx)
{
    union term *f;
    f = parse_fun(src, ctx);
    if (!f)
        error("parse error function\n");
    while (1) {
        union term *a = parse_fun(src, ctx);
        if (!a)
            return f;
        struct app *ap = malloc(sizeof(union term));
        ap->tag = tapp;
        ap->fun = f;
        ap->arg = a;
        f = (union term *)ap;
    }
}

union term *parse(FILE *src)
{
    struct ctx root = {
        .pos = 0,
        .len = 0,
        .binding = NULL,
        .next = &root,
    };
    return parse_term(src, &root);
}

void print_term(FILE *dst, FILE *src, union term *t, struct ctx *ctx, int lapp);

void print_var(FILE *dst, FILE *src, struct var *v, struct ctx *ctx)
{
    if (src) {
        int i;
        char buf[32];
        for (i = 0; i < v->idx; i++)
            ctx = ctx->next;
        fsetpos(src, &ctx->pos);
        if (!get_id(src, buf))
            error("error\n");
        fputs(buf, dst);
    } else {
        fprintf(dst, "%d", v->idx);
    }
}

void print_abs(FILE *dst, FILE *src, struct abs *ab, struct ctx *ctx)
{
    char buf[32];
    if (src) {
        fsetpos(src, &ab->pos);
        if (!get_id(src, buf))
            error("error\n");
        fputs("lambda ", dst);
        fputs(buf, dst);
        fputs(".", dst);
    } else {
        fputs("lambda.", dst);
    }
    ctx = push_ctx(ctx, ab->pos);
    print_term(dst, src, ab->exp, ctx, 0);
    ctx = pop_ctx(ctx);
}

void print_fun(FILE *dst, FILE *src, union term *fun, struct ctx *ctx) {
    switch (fun->tag) {
    case tabs:
        print_abs(dst, src, &fun->ab, ctx);
        return;
    case tvar:
        print_var(dst, src, &fun->v, ctx);
        return;
    default:
        error("hoge");
    }
}

void print_term(FILE *dst, FILE *src, union term *t, struct ctx *ctx, int lapp)
{
    if (t->tag == tapp) {
        struct app *ap = &t->ap;
        if (ap->fun->tag == tabs) {
            fputs("(", dst);
            print_fun(dst, src, ap->fun, ctx);
            fputs(")", dst);
        } else if (ap->fun->tag == tvar) {
            print_fun(dst, src, ap->fun, ctx);
        } else {
            print_term(dst, src, ap->fun, ctx, 1);
        }
        fputs(" ", dst);
        if (ap->arg->tag == tapp || (ap->arg->tag == tabs && lapp)) {
            fputs("(", dst);
            print_term(dst, src, ap->arg, ctx, 0);
            fputs(")", dst);
        } else {
            print_term(dst, src, ap->arg, ctx, 0);
        }
    } else {
        print_fun(dst, src, t, ctx);
    }
}

int print(FILE *dst, FILE *src, union term *t)
{
    struct ctx root = {
        .pos = 0,
        .len = 0,
        .binding = NULL,
        .next = &root,
    };
    print_term(dst, src, t, &root, 0);
    return fputs("\n", dst);
}

union term *shift(union term *t, int d, int c)
{
    switch (t->tag) {
    case tapp:
        t->ap.fun = shift(t->ap.fun, d, c);
        t->ap.arg = shift(t->ap.arg, d, c); return t; case tabs:
        t->ab.exp = shift(t->ab.exp, d, c+1);
        return t;
    case tvar:
        if (t->v.idx >= c)
            t->v.idx += d;
        return t;
    }
    error("invalid term\n");
}

union term *copy(union term *t)
{
    union term *d = malloc(sizeof(union term));
    memcpy(d, t, sizeof(union term));
    switch (t->tag) {
    case tapp:
        d->ap.fun = copy(t->ap.fun);
        d->ap.arg = copy(t->ap.arg);
        return d;
    case tabs:
        d->ab.exp = copy(t->ab.exp);
        return d;
    case tvar:
        return d;
    }
    error("invalid term\n");
}

union term *subst(union term *t, int j, int c, union term *s)
{
    switch (t->tag) {
    case tapp:
        t->ap.fun = subst(t->ap.fun, j, c, s);
        t->ap.arg = subst(t->ap.arg, j, c, s);
        return t;
    case tabs:
        t->ab.exp = subst(t->ab.exp, j, c+1, s);
        return t;
    case tvar:
        if (t->v.idx == j+c) {
            union term *ss = copy(s);
            free(t);
            return shift(ss, c, 0);
        }
        return t;
    }
    error("invalid term\n");
}

union term *subst1(union term *t, union term *s)
{
    s = shift(s, 1, 0);
    t = subst(t, 0, 0, s);
    t = shift(t, -1, 0);
    return t;
}

int isval(union term *t)
{
    return t->tag == tabs;
}

union term *eval1(union term *t, jmp_buf jb)
{
    if (t->tag == tapp) {
        struct app *ap = &t->ap;
        if (ap->fun->tag == tabs && isval(ap->arg)) {
            debug(" -> E-APPABS");
            t = subst1(ap->fun->ab.exp, ap->arg);
            free(ap->fun);
            free(ap->arg);
            free(ap);
            return t;
        } else if (isval(ap->fun)) {
            debug(" -> E-APP2");
            ap->arg = eval1(ap->arg, jb);
            return t;
        } else {
            debug(" -> E-APP1");
            ap->fun = eval1(ap->fun, jb);
            return t;
        }
    }
    debug(" -> [no rule]\n");
    longjmp(jb, 1);
}

union term *eval(union term *t)
{
    jmp_buf jb;
    while (!setjmp(jb)) {
        dbg && print(dbg, NULL, t);
        t = eval1(t, jb);
        debug("\n");
    }
    return t;
}

FILE *read(void)
{
    FILE *tmp = tmpfile();
    int c;
    while ((c = getchar()) !=  EOF)
        fputc(c, tmp);
    rewind(tmp);
    return tmp;
}

int main(int argc, char **argv)
{
#ifdef DEBUG
    dbg = stderr;
#endif
    FILE *tmp = read();
    union term *t = parse(tmp);
    t = eval(t);
    print(stdout, tmp, t);
    return 0;
}
