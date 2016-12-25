#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include <ctype.h>
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
};

union term {
    enum tag tag;
    struct var v;
    struct abs ab;
    struct app ap;
};


FILE *dbg;

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
    } while (isalnum(c) || c == '_');
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
        error(". is expected");
    ctx = push_ctx(ctx, p);
    union term *e = parse_term(src, ctx);
    if (!e)
        error("exp parse error");
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
    struct ctx *def = find_ctx(ctx, src, buf);
    fsetpos(src, &save);
    if (!def)
        error("undefined");
    struct var *v = malloc(sizeof(union term));
    v->tag = tvar;
    v->len = ctx->len;
    v->idx = ctx->len - def->len;
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
            error("unmatch paren");
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
        error("fun");
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


void print_term(FILE *dst, FILE *src, union term *t, struct ctx *ctx);

void print_var(FILE *dst, FILE *src, struct var *v, struct ctx *ctx)
{
    int i;
    char buf[32];
    for (i = 0; i < v->idx; i++)
        ctx = ctx->next;
    fsetpos(src, &ctx->pos);
    if (!get_id(src, buf))
        error("error");
    fprintf(dst, "%s[%d]", buf, v->idx);
}

void print_abs(FILE *dst, FILE *src, struct abs *ab, struct ctx *ctx)
{
    char buf[32];
    fsetpos(src, &ab->pos);
    if (!get_id(src, buf))
        error("error");
    fprintf(dst, "(lambda %s.", buf);
    ctx = push_ctx(ctx, ab->pos);
    print_term(dst, src, ab->exp, ctx);
    ctx = pop_ctx(ctx);
    fprintf(dst, ")");
}

void print_app(FILE *dst, FILE *src, struct app *ap, struct ctx *ctx)
{
    fprintf(dst, "(");
    print_term(dst, src, ap->fun, ctx);
    fprintf(dst, " ");
    print_term(dst, src, ap->arg, ctx);
    fprintf(dst, ")");
}

void print_term(FILE *dst, FILE *src, union term *t, struct ctx *ctx)
{
    switch (t->tag) {
    case tapp:
        print_app(dst, src, &t->ap, ctx);
        break;
    case tabs:
        print_abs(dst, src, &t->ab, ctx);
        break;
    case tvar:
        print_var(dst, src, &t->v, ctx);
        break;
    }
}

void print(FILE *dst, FILE *src, union term *t)
{
    struct ctx root = {
        .pos = 0,
        .len = 0,
        .binding = NULL,
        .next = &root,
    };
    print_term(dst, src, t, &root);
    fputs("\n", dst);
}

union term *shift(union term *t, int d, int c)
{
    switch (t->tag) {
    case tapp:
        t->ap.fun = shift(t->ap.fun, d, c);
        t->ap.arg = shift(t->ap.arg, d, c);
        return t;
    case tabs:
        t->ab.exp = shift(t->ab.exp, d, c+1);
        return t;
    case tvar:
        if (t->v.idx >= c)
            t->v.idx += d;
        return t;
    }
    error("invalid term");
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
    error("invalid term");
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
            debug("beta kanyaku!\n");
            union term *ss = copy(s);
            return shift(ss, c, 0); /* ap->arg and top ap/ab is eliminated */
        }
        return t;
    }
    error("invalid term");
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
            return subst1(ap->fun->ab.exp, ap->arg); /* ap->arg and top ap/ab is eliminated */
        } else if (isval(ap->fun)) {
            ap->arg = eval1(ap->arg, jb);
            return t;
        } else {
            ap->fun = eval1(ap->fun, jb);
            return t;
        }
    }
    longjmp(jb, 1);
}

union term *eval(union term *t)
{
    jmp_buf jb;
    while (!setjmp(jb))
        t = eval1(t, jb);
    return t;
}


int main(int argc, char **argv)
{
    dbg = stderr;
    FILE *tmp = tmpfile();
    int c;
    while ((c = getchar()) !=  EOF)
        fputc(c, tmp);
    rewind(tmp);
    union term *t = parse(tmp);
    t = eval(t);
    print(stdout, tmp, t);
    return 0;
}
