#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include <ctype.h>

FILE *dbg;
#define error(...) (fprintf(stderr, __VA_ARGS__), exit(1))
#define debug(...) (dbg && fprintf(dbg, __VA_ARGS__))

union type;
union term;
enum tmtag {tmabs, tmapp, tmvar, tmtrue, tmfalse, tmif};
enum tytag {tybool, tyarr};

struct ctx {
    fpos_t pos;
    int len;
    union type *ty;
    struct ctx *next;
};

struct var {
    enum tmtag tag;
    fpos_t pos;
    int idx;
    int len;
};

struct abs {
    enum tmtag tag;
    fpos_t pos;
    union type *ty;
    union term *exp;
};

struct app {
    enum tmtag tag;
    fpos_t pos;
    union term *fun;
    union term *arg;
};

struct _if {
    enum tmtag tag;
    fpos_t pos;
    union term *cond;
    union term *then;
    union term *_else;
};

union term {
    enum tmtag tag;
    fpos_t pos;
    struct var v;
    struct abs ab;
    struct app ap;
    struct _if _if;
};

struct arr {
    enum tytag tag;
    fpos_t pos;
    union type *from;
    union type *to;
};

union type {
    enum tytag tag;
    fpos_t pos;
    struct arr ar;
};

static union type static_tybool = {.tag = tybool};

fpos_t get_fpos(FILE *src)
{
    fpos_t pos;
    fgetpos(src, &pos);
    return pos;
}

void set_fpos(FILE *src, fpos_t pos)
{
    fsetpos(src, &pos);
}

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
    fpos_t save;
    skip_spaces(src);
    fgetpos(src, &save);
    if (!match_str(src, id))
        goto mismatch;
    int c = fgetc(src);
    if (isalnum(c) || c == '_')
        goto mismatch;
    ungetc(c, src);
    return 1;
mismatch:
    fsetpos(src, &save);
    return 0;
}

char *get_id(FILE *src, char *id)
{
    char *p = id;
    int c = fgetc(src);
    if (!(isalpha(c) || c == '_')) {
        ungetc(c, src);
        return NULL;
    }
    do {
        *p++ = c;
        c = fgetc(src);
    } while (p - id < 32 && (isalnum(c) || c == '_'));
    if (p - id >= 32)
        error("too long identifier!\n");
    ungetc(c, src);
    *p = '\0';
    return id;
}

union term *parse_term(FILE *src, struct ctx *ctx);

struct ctx *get_ctx(struct ctx *ctx, int idx)
{
    if (ctx->next == ctx)
        return NULL;
    if (idx == 0)
        return ctx;
    return get_ctx(ctx->next, idx-1);
}

struct ctx *find_ctx(struct ctx *ctx, FILE *src, char *id)
{
    if (ctx->next == ctx)
        return NULL;
    fsetpos(src, &ctx->pos);
    if (match_id(src, id))
        return ctx;
    return find_ctx(ctx->next, src, id);
}

struct ctx *push_ctx(struct ctx *ctx, fpos_t pos, union type *ty) {
    struct ctx *top = malloc(sizeof(struct ctx));
    top->pos = pos;
    top->next = ctx;
    top->ty = ty;
    top->len = ctx->len + 1;
    return top;
}

struct ctx *pop_ctx(struct ctx *ctx)
{
    struct ctx *next = ctx->next;
    free(ctx);
    return next;
}

union type *parse_type(FILE *src, struct ctx *ctx);

union type *parse_bool(FILE *src, struct ctx *ctx)
{
    skip_spaces(src);
    if (!match_id(src, "Bool"))
        return NULL;
    return &static_tybool;
}

union type *parse_type1(FILE *src, struct ctx *ctx)
{
    union type *ty;
    skip_spaces(src);
    if (match_str(src, "(")) {
        skip_spaces(src);
        ty = parse_type(src, ctx);
        if (!match_str(src, ")"))
            error("paren is not closed\n");
        return ty;
    }
    return parse_bool(src, ctx);
}

union type *parse_type(FILE *src, struct ctx *ctx)
{
    union type *ty = parse_type1(src, ctx);
    if (!ty)
        error("parse error\n");
    skip_spaces(src);
    if (!match_str(src, "->"))
        return ty;
    union type *to = parse_type(src, ctx);
    if (!to)
        error("parse error\n");
    struct arr *ar = malloc(sizeof(union type));
    ar->tag = tyarr;
    ar->from = ty;
    ar->to = to;
    return (union type *)ar;
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
        error("invalid identifier\n");
    skip_spaces(src);
    if (!match_str(src, ":"))
        error(": is expected\n");
    union type *ty = parse_type(src, ctx);
    if (!ty)
        error("invalid type identifier\n");
    skip_spaces(src);
    if (!match_str(src, "."))
        fgetpos(src, &p),error(". is expected %lld\n", p);
    ctx = push_ctx(ctx, p, ty);
    union term *e = parse_term(src, ctx);
    if (!e)
        error("parse error\n");
    struct abs *ab = malloc(sizeof(union term));
    ab->tag = tmabs;
    ab->pos = p;
    ab->ty = ty;
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
    save = get_fpos(src);
    if (!get_id(src, buf))
        goto invalid;
    if (!strcmp(buf, "then") || !strcmp(buf, "else"))
        goto invalid;
    fgetpos(src, &save);
    struct ctx *hit = find_ctx(ctx, src, buf);
    fsetpos(src, &save);
    if (!hit)
        error("undefined identifier %s\n", buf);
    struct var *v = malloc(sizeof(union term));
    v->tag = tmvar;
    v->len = ctx->len;
    v->idx = ctx->len - hit->len;
    return v;
invalid:
    set_fpos(src, save);
    return NULL;

}

struct _if *parse_if(FILE *src, struct ctx *ctx)
{
    skip_spaces(src);
    if (!match_id(src, "if"))
        return NULL;
    union term *cond = parse_term(src, ctx);
    if (!cond)
        error("invalid condition\n");
    skip_spaces(src);
    if (!match_id(src, "then"))
        error("then is expected %lld\n", get_fpos(src));
    union term *then = parse_term(src, ctx);
    if (!then)
        error("invalid exp in then\n");
    skip_spaces(src);
    if (!match_id(src, "else"))
        error("else is expected\n");
    union term *_else = parse_term(src, ctx);
    if (!_else)
        error("invalid exp in else\n");
    struct _if *_if = malloc(sizeof(union term));
    _if->tag = tmif;
    _if->cond = cond;
    _if->then = then;
    _if->_else = _else;
    return _if;
}

union term *parse_true(FILE *src, struct ctx *ctx)
{
    skip_spaces(src);
    if (!match_id(src, "true")) {
        return NULL;
    }
    union term *tru = malloc(sizeof(union term));
    tru->tag = tmtrue;
    return tru;
}

union term *parse_false(FILE *src, struct ctx *ctx)
{
    skip_spaces(src);
    if (!match_id(src, "false"))
        return NULL;
    union term *fls = malloc(sizeof(union term));
    fls->tag = tmfalse;
    return fls;
}

union term *parse_fun(FILE *src, struct ctx *ctx)
{
    union term *f;
    skip_spaces(src);
    if (match_str(src, "(")) {
        skip_spaces(src);
        f = parse_term(src, ctx);
        skip_spaces(src);
        if (!match_str(src, ")"))
            error("paren is not closed\n");
        return f;
    }
    f = (union term *)parse_abs(src, ctx);
    if (f)
        return f;
    f = (union term *)parse_if(src, ctx);
    if (f)
        return f;
    f = (union term *)parse_true(src, ctx);
    if (f)
        return f;
    f = (union term *)parse_false(src, ctx);
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
    while (f->tag == tmvar || f->tag == tmapp || f->tag == tmabs) {
        union term *a = parse_fun(src, ctx);
        if (!a)
            return f;
        struct app *ap = malloc(sizeof(union term));
        ap->tag = tmapp;
        ap->fun = f;
        ap->arg = a;
        f = (union term *)ap;
    }
    return f;
}

union term *parse(FILE *src)
{
    struct ctx root = {
        .pos = 0,
        .len = 0,
        .ty = NULL,
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

void print_type(FILE *dst, FILE *src, union type *ty, struct ctx *ctx)
{
    switch (ty->tag) {
    case tybool:
        fputs("Bool", dst);
        return;
    case tyarr:
        if (ty->ar.from->tag == tyarr) {
            fputs("(", dst);
            print_type(dst, src, ty->ar.from, ctx);
            fputs(")", dst);
        } else {
            print_type(dst, src, ty->ar.from, ctx);
        }
        fputs("->", dst);
        print_type(dst, src, ty->ar.to, ctx);
        return;
    default:
        error("invalid type\n");
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
        fputs(":", dst);
        print_type(dst, src, ab->ty, ctx);
        fputs(".", dst);
    } else {
        fputs("lambda", dst);
        fputs(":", dst);
        print_type(dst, src, ab->ty, ctx);
        fputs(".", dst);
    }
    ctx = push_ctx(ctx, ab->pos, ab->ty);
    print_term(dst, src, ab->exp, ctx, 0);
    ctx = pop_ctx(ctx);
}

void print_fun(FILE *dst, FILE *src, union term *fun, struct ctx *ctx) {
    switch (fun->tag) {
    case tmabs:
        print_abs(dst, src, &fun->ab, ctx);
        return;
    case tmvar:
        print_var(dst, src, &fun->v, ctx);
        return;
    case tmif:
        fputs("if ", dst);
        print_term(dst, src, fun->_if.cond, ctx, 0);
        fputs(" then ", dst);
        print_term(dst, src, fun->_if.then, ctx, 0);
        fputs(" else ", dst);
        print_term(dst, src, fun->_if._else, ctx, 0);
        return;
    case tmtrue:
        fputs("true", dst);
        return;
    case tmfalse:
        fputs("false", dst);
        return;
    default:
        error("hoge");
    }
}

void print_term(FILE *dst, FILE *src, union term *t, struct ctx *ctx, int lapp)
{
    if (t->tag == tmapp) {
        struct app *ap = &t->ap;
        if (ap->fun->tag == tmabs) {
            fputs("(", dst);
            print_fun(dst, src, ap->fun, ctx);
            fputs(")", dst);
        } else if (ap->fun->tag == tmvar) {
            print_fun(dst, src, ap->fun, ctx);
        } else {
            print_term(dst, src, ap->fun, ctx, lapp+1);
        }
        fputs(" ", dst);
        if (ap->arg->tag == tmapp || (ap->arg->tag == tmabs && lapp)) {
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

int print(FILE *dst, FILE *src, union term *tm, union type *ty)
{
    struct ctx root = {
        .pos = 0,
        .len = 0,
        .ty = NULL,
        .next = &root,
    };
    print_term(dst, src, tm, &root, 0);
    if (ty) {
        fputs(":", dst);
        print_type(dst, src, ty, &root);
    }
    return fputs("\n", dst);
}

union term *shift(union term *t, int d, int c)
{
    switch (t->tag) {
    case tmapp:
        t->ap.fun = shift(t->ap.fun, d, c);
        t->ap.arg = shift(t->ap.arg, d, c);
        return t;
    case tmabs:
        t->ab.exp = shift(t->ab.exp, d, c+1);
        return t;
    case tmvar:
        if (t->v.idx >= c)
            t->v.idx += d;
        return t;
    case tmif:
        t->_if.cond = shift(t->_if.cond, d, c);
        t->_if.then = shift(t->_if.then, d, c);
        t->_if._else = shift(t->_if._else, d, c);
        return t;
    case tmtrue:
    case tmfalse:
        return t;
    }
    error("invalid term\n");
}

union term *copy(union term *t)
{
    union term *d = malloc(sizeof(union term));
    memcpy(d, t, sizeof(union term));
    switch (t->tag) {
    case tmapp:
        d->ap.fun = copy(t->ap.fun);
        d->ap.arg = copy(t->ap.arg);
        return d;
    case tmabs:
        d->ab.exp = copy(t->ab.exp);
        /* d->ab.ty??? */
        return d;
    case tmif:
        d->_if.cond = copy(t->_if.cond);
        d->_if.then = copy(t->_if.then);
        d->_if._else = copy(t->_if._else);
        return d;
    case tmtrue:
    case tmfalse:
    case tmvar:
        return d;
    }
    error("invalid term\n");
}

union term *subst(union term *t, int j, int c, union term *s)
{
    switch (t->tag) {
    case tmapp:
        t->ap.fun = subst(t->ap.fun, j, c, s);
        t->ap.arg = subst(t->ap.arg, j, c, s);
        return t;
    case tmabs:
        t->ab.exp = subst(t->ab.exp, j, c+1, s);
        return t;
    case tmvar:
        if (t->v.idx == j+c) {
            union term *ss = copy(s);
            free(t);
            return shift(ss, c, 0);
        }
        return t;
    case tmif:
        t->_if.cond = subst(t->_if.cond, j, c, s);
        t->_if.then = subst(t->_if.then, j, c, s);
        t->_if._else = subst(t->_if._else, j, c, s);
        return t;
    case tmtrue:
    case tmfalse:
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
    return t->tag == tmabs || t->tag == tmtrue || t->tag == tmfalse;
}

union term *eval1(union term *t, jmp_buf jb)
{
    union term *tmp;
    struct app *ap;
    switch (t->tag) {
    case tmapp:
        ap = &t->ap;
        if (ap->fun->tag == tmabs && isval(ap->arg)) {
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
    case tmif:
        switch (t->_if.cond->tag) {
        case tmtrue:
            debug(" -> E-IFTRUE");
            tmp = t->_if.then;
            free(t->_if.cond);
            free(t->_if._else);
            free(t);
            return tmp;
        case tmfalse:
            debug(" -> E-IFFALSE");
            tmp = t->_if._else;
            free(t->_if.cond);
            free(t->_if.then);
            free(t);
            return tmp;
        default:
            debug(" -> E-IF");
            t->_if.cond = eval1(t->_if.cond, jb);
            return t;
        }
    default:
        debug(" -> [no rule]\n");
        longjmp(jb, 1);
    }
}

union term *eval(union term *t)
{
    jmp_buf jb;
    while (!setjmp(jb)) {
        dbg && print(dbg, NULL, t, NULL);
        t = eval1(t, jb);
        debug("\n");
    }
    return t;
}

int equal_type(union type *ty1, union type *ty2)
{
    if (ty1->tag != ty2->tag)
        return 0;
    if (ty1->tag == tyarr)
        return equal_type(ty1->ar.from, ty2->ar.from) && equal_type(ty1->ar.to, ty2->ar.to);
    return 1;
}

union type *get_type(union term *t, struct ctx *ctx)
{
    switch (t->tag) {
    case tmvar:
        return get_ctx(ctx, t->v.idx)->ty;
    case tmabs:
        {
            ctx = push_ctx(ctx, t->ab.pos, t->ab.ty);
            union type *to = get_type(t->ab.exp, ctx);
            ctx = pop_ctx(ctx);
            struct arr *ar = malloc(sizeof(union type));
            ar->tag = tyarr;
            ar->from = t->ab.ty;
            ar->to = to;
            return (union type *)ar;
        }
    case tmapp:
        {
            struct arr *tfun = (struct arr *)get_type(t->ap.fun, ctx);
            union type *targ = get_type(t->ap.arg, ctx);
            if (tfun->tag != tyarr)
                error("arrow type expected\n");
            if (!equal_type(tfun->from, targ))
                error("parameter type mismatch\n");
            return tfun->to;
        }
    case tmtrue:
    case tmfalse:
        return &static_tybool;
    case tmif:
        if (equal_type(get_type(t->_if.cond, ctx), &static_tybool)) {
            union type *ty = get_type(t->_if.then, ctx);
            if (equal_type(ty, get_type(t->_if._else, ctx)))
                return ty;
            else
                error("arms of conditional have different types\n");
        } else {
            error("guard of conditional not a boolean types\n");
        }
    default:
        error("invalid type\n");
    }
}

union type *check_type(union term *t)
{
    struct ctx root = {
        .pos = 0,
        .len = 0,
        .ty = NULL,
        .next = &root,
    };
    return get_type(t, &root);
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
    // dbg = stderr;
    FILE *tmp = read();
    union term *tm = parse(tmp);
    if (!tm)
        error("parse error!\n");
    union type *ty = check_type(tm);
    tm = eval(tm);
    print(stdout, tmp, tm, ty);
    return 0;
}
