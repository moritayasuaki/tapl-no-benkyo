#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include <ctype.h>

#define LAMBDA "\\"
#define FORALL "^"
#define UNIV   "*"

FILE *dbg;
jmp_buf eh;

#define error(...)  (fprintf(stderr, __VA_ARGS__), exit(1))
#define debug(...)  (dbg && fprintf(dbg, __VA_ARGS__))
#define bug()       error("%s:%d:%s BUG!\n", __FILE__, __LINE__, __func__)

union term;
struct ctx;
enum  ttag {tvar, tuniv, tapp, tabs, tprod};

#define thead struct {enum ttag tag;fpos_t pos;}

struct ctx {
    int len;
    struct bind *bind;
};

struct bind {
    fpos_t pos;
    int refcnt;
    union term *type;
    union term *term;
};

struct var {
    thead;
    int idx;
    int len;
};

struct app {
    thead;
    union term *fun;
    union term *arg;
};

struct abs {
    thead;
    union term *type;
    union term *exp;
};

struct prod {
    thead;
    union term *type;
    union term *exp;
};

struct univ {
    thead;
    int level;
};

union term {
    thead;
    struct var var;
    struct abs abs;
    struct app app;
    struct prod prod;
    struct univ univ;
};

union term *parse(FILE *src);
union term *parse_term(FILE *src, struct ctx *ctx);
void print(FILE *dst, FILE *src, union term *t);
void print_term(FILE *dst, FILE *src, union term *t, struct ctx *ctx, int lapp);

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
    skip_spaces(src);
    fpos_t save = get_fpos(src);
    while (*str)
        if (fgetc(src) != *str++)
            goto mismatch;
    return 1;
mismatch:
    set_fpos(src, save);
    return 0;
}

int match_id(FILE *src, char *id)
{
    skip_spaces(src);
    fpos_t save = get_fpos(src);
    if (!match_str(src, id))
        goto mismatch;
    int c = fgetc(src);
    if (isalnum(c) || c == '_')
        goto mismatch;
    ungetc(c, src);
    return 1;
mismatch:
    set_fpos(src, save);
    return 0;
}

char *get_id(FILE *src, char *id)
{
    skip_spaces(src);
    fpos_t save = get_fpos(src);
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

void push_bind(struct ctx *ctx, fpos_t pos, union term *type, union term *term)
{
    int len = ctx->len;
    struct bind *bind = ctx->bind;
    bind = realloc(bind, (len + 1) * sizeof(struct bind));
    if (!bind)
        error("no memory\n");
    bind[len].pos = pos;
    bind[len].type = type;
    bind[len].term = term;
    bind[len].refcnt = 0;
    ctx->bind = bind;
    ctx->len = len + 1;
}

void pop_bind(struct ctx *ctx)
{
    int len = ctx->len;
    struct bind *bind = ctx->bind;
    if (len - 1)
        bind = realloc(bind, (len - 1) * sizeof(struct bind));
    else
        free(bind), bind = NULL;
    ctx->bind = bind;
    ctx->len = len - 1;
}

struct bind *get_bind(struct ctx *ctx, int idx)
{
    int len = ctx->len;
    struct bind *bind = ctx->bind;
    if (0 <= idx && idx < len) {
        return &bind[len - (idx + 1)];
    }
    return NULL;
}

struct bind *find_bind(struct ctx *ctx, FILE *src, char *id)
{
    int len = ctx->len;
    struct bind *bind = ctx->bind;
    fpos_t save = get_fpos(src);
    while (len--) {
        set_fpos(src, bind[len].pos);
        if (match_id(src, id)) {
            set_fpos(src, save);
            return &bind[len];
        }
    }
    set_fpos(src, save);
    return NULL;
}

int get_idx(struct ctx *ctx, struct bind *bind)
{
    int len = ctx->len;
    int idx = len - (bind - ctx->bind + 1);
    return idx;
}

void del_bind(struct ctx *ctx, struct bind *bind)
{
    int idx = get_idx(ctx, bind);
    memmove(bind, bind + 1, idx * sizeof(struct ctx));
    pop_bind(ctx);
}

struct prod *parse_prod(FILE *src, struct ctx *ctx)
{
    char buf[32];
    if (!match_str(src, FORALL))
        return NULL;
    skip_spaces(src);
    fpos_t pos = get_fpos(src);
    if (!get_id(src, buf))
        error("invalid identifier\n");
    if (!match_str(src, ":"))
        error(": is expected\n");
    union term *type = parse_term(src, ctx);
    if (!type)
        error("invalid type\n");
    if (!match_str(src, "->"))
        error("-> is expected %lld\n", get_fpos(src));
    push_bind(ctx, pos, type, NULL);
    union term *exp = parse_term(src, ctx);
    if (!exp)
        error("invaid expression\n");
    struct prod *prod = malloc(sizeof(union term));
    prod->tag = tprod;
    prod->pos = pos;
    prod->type = type;
    prod->exp = exp;
    pop_bind(ctx);
    return prod;
}

struct abs *parse_abs(FILE *src, struct ctx *ctx)
{
    char buf[32];
    if (!match_str(src, LAMBDA))
        return NULL;
    skip_spaces(src);
    fpos_t pos = get_fpos(src);
    if (!get_id(src, buf))
        error("invalid identifier\n");
    if (!match_str(src, ":"))
        error(": is expected\n");
    union term *type = parse_term(src, ctx);
    if (!type)
        error("invalid type expression\n");
    if (!match_str(src, "."))
        error(". is expected %lld\n", get_fpos(src));
    push_bind(ctx, pos, type, NULL);
    union term *exp = parse_term(src, ctx);
    if (!exp)
        error("invalid expression\n");
    struct abs *abs = malloc(sizeof(union term));
    abs->tag = tabs;
    abs->pos = pos;
    abs->type = type;
    abs->exp = exp;
    pop_bind(ctx);
    return abs;
}

struct univ *parse_univ(FILE *src, struct ctx *ctx)
{
    if (!match_str(src, UNIV))
        return NULL;
    int level = 0;
    while (match_str(src, UNIV))
        level++;
    struct univ *univ = malloc(sizeof(union term));
    univ->tag = tuniv;
    univ->pos = get_fpos(src);
    univ->level = level;
    return univ;
}

struct var *parse_var(FILE *src, struct ctx *ctx)
{
    char buf[32];
    skip_spaces(src);
    fpos_t pos = get_fpos(src);
    if (!get_id(src, buf))
        goto invalid;
    struct bind *bind = find_bind(ctx, src, buf);
    if (!bind)
        error("undefined identifier %s\n", buf);
    bind->refcnt++;
    int idx = get_idx(ctx, bind);
    struct var *var = malloc(sizeof(union term));
    var->tag = tvar;
    var->len = ctx->len;
    var->idx = idx;
    return var;
invalid:
    set_fpos(src, pos);
    return NULL;
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
    f = (union term *)parse_prod(src, ctx);
    if (f)
        return f;
    f = (union term *)parse_univ(src, ctx);
    if (f)
        return f;
    f = (union term *)parse_var(src, ctx);
    if (f)
        return f;
    return NULL;
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
        struct app *app = malloc(sizeof(union term));
        app->tag = tapp;
        app->fun = f;
        app->arg = a;
        f = (union term *)app;
    }
    return f;
}

union term *parse(FILE *src)
{
    struct ctx ctx = {0};
    return parse_term(src, &ctx);
}

void print_var(FILE *dst, FILE *src, struct var *var, struct ctx *ctx)
{
    if (src) {
        fpos_t save = get_fpos(src);
        char buf[32];
        struct bind *bind = get_bind(ctx, var->idx);
        set_fpos(src, bind->pos);
        if (!get_id(src, buf))
            error("error\n");
        fputs(buf, dst);
        set_fpos(src, save);
    } else {
        fprintf(dst, "%d", var->idx);
    }
}

void print_univ(FILE *dst, FILE *src, struct univ *univ, struct ctx *ctx)
{
    int level = univ->level;
    fputs(UNIV, dst);
    while (level--)
        fputs(UNIV, dst);
}

void print_prod(FILE *dst, FILE *src, struct prod *prod, struct ctx *ctx)
{
    char buf[32];
    if (src) {
        fpos_t save = get_fpos(src);
        set_fpos(src, prod->pos);
        if (!get_id(src, buf))
            error("error\n");
        fputs(FORALL, dst);
        fputs(buf, dst);
        fputs(":", dst);
        print_term(dst, src, prod->type, ctx, 0);
        fputs("->", dst);
        set_fpos(src, save);
    } else {
        fputs(FORALL, dst);
        fputs(":", dst);
        print_term(dst, src, prod->type, ctx, 0);
        fputs("->", dst);
    }
    push_bind(ctx, prod->pos, prod->type, NULL);
    print_term(dst, src, prod->exp, ctx, 0);
    pop_bind(ctx);
}

void print_abs(FILE *dst, FILE *src, struct abs *abs, struct ctx *ctx)
{
    char buf[32];
    if (src) {
        fpos_t save = get_fpos(src);
        set_fpos(src, abs->pos);
        if (!get_id(src, buf))
            error("error\n");
        fputs(LAMBDA, dst);
        fputs(buf, dst);
        fputs(":", dst);
        print_term(dst, src, abs->type, ctx, 0);
        fputs(".", dst);
        set_fpos(src, save);
    } else {
        fputs(LAMBDA, dst);
        fputs(":", dst);
        print_term(dst, src, abs->type, ctx, 0);
        fputs(".", dst);
    }
    push_bind(ctx, abs->pos, abs->type, NULL);
    print_term(dst, src, abs->exp, ctx, 0);
    pop_bind(ctx);
}

void print_fun(FILE *dst, FILE *src, union term *fun, struct ctx *ctx) {
    switch (fun->tag) {
    case tvar:
        print_var(dst, src, &fun->var, ctx);
        return;
    case tuniv:
        print_univ(dst, src, &fun->univ, ctx);
        return;
    case tabs:
        print_abs(dst, src, &fun->abs, ctx);
        return;
    case tprod:
        print_prod(dst, src, &fun->prod, ctx);
        return;
    default:
        bug();
    }
}

void print_term(FILE *dst, FILE *src, union term *t, struct ctx *ctx, int lapp)
{
    if (t->tag == tapp) {
        struct app *app = &t->app;
        if (app->fun->tag == tabs || app->fun->tag == tprod) {
            fputs("(", dst);
            print_fun(dst, src, app->fun, ctx);
            fputs(")", dst);
        } else if (app->fun->tag == tapp) {
            print_term(dst, src, app->fun, ctx, lapp+1);
        } else {
            print_fun(dst, src, app->fun, ctx);
        }
        fputs(" ", dst);
        if (app->arg->tag == tapp || ((app->arg->tag == tabs || app->arg->tag == tprod) && lapp)) {
            fputs("(", dst);
            print_term(dst, src, app->arg, ctx, 0);
            fputs(")", dst);
        } else {
            print_term(dst, src, app->arg, ctx, 0);
        }
    } else {
        print_fun(dst, src, t, ctx);
    }
}

void print(FILE *dst, FILE *src, union term *term)
{
    struct ctx ctx = {0};
    print_term(dst, src, term, &ctx, 0);
    fputs("\n", dst);
}

union term *shift(union term *t, int d, int c)
{
    switch (t->tag) {
    case tvar:
        if (t->var.idx >= c)
            t->var.idx += d;
        return t;
    case tuniv:
        return t;
    case tabs:
        t->abs.exp = shift(t->abs.exp, d, c+1);
        return t;
    case tprod:
        t->prod.exp = shift(t->prod.exp, d, c+1);
        return t;
    case tapp:
        t->app.fun = shift(t->app.fun, d, c);
        t->app.arg = shift(t->app.arg, d, c);
        return t;
    default:
        bug();
    }
}

union term *copy(union term *t)
{
    union term *d = malloc(sizeof(union term));
    memcpy(d, t, sizeof(union term));
    switch (t->tag) {
    case tvar:
        return d;
    case tuniv:
        return d;
    case tabs:
        d->abs.type = copy(t->abs.type);
        d->abs.exp = copy(t->abs.exp);
        return d;
    case tprod:
        d->prod.type = copy(t->prod.type);
        d->prod.exp = copy(t->prod.exp);
        return d;
    case tapp:
        d->app.fun = copy(t->app.fun);
        d->app.arg = copy(t->app.arg);
        return d;
    default:
        bug();
    }
}

void delete(union term *t)
{
    switch (t->tag) {
    case tvar:
        free(t);
        return;
    case tuniv:
        free(t);
        return;
    case tabs:
        delete(t->abs.type);
        delete(t->abs.exp);
        free(t);
        return;
    case tprod:
        delete(t->prod.type);
        delete(t->prod.exp);
        free(t);
        return;
    case tapp:
        delete(t->app.fun);
        delete(t->app.arg);
        free(t);
        return;
    default:
        bug();
    }
}

union term *subst(union term *t, int j, int c, union term *s)
{
    switch (t->tag) {
    case tvar:
        if (t->var.idx == j+c) {
            union term *tmp = copy(s);
            free(t);
            t = tmp;
            return shift(t, c, 0);
        }
        return t;
    case tuniv:
        return t;
    case tabs:
        t->abs.exp = subst(t->abs.exp, j, c+1, s);
        return t;
    case tprod:
        t->prod.exp = subst(t->prod.exp, j, c+1, s);
        return t;
    case tapp:
        t->app.fun = subst(t->app.fun, j, c, s);
        t->app.arg = subst(t->app.arg, j, c, s);
        return t;
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

int isdeltavar(struct ctx *ctx, union term *t)
{
    return t->tag == tvar && get_bind(ctx, t->var.idx)->term;
}

union term *delta(struct ctx *ctx, union term *t, jmp_buf jb)
{
    assert(isdeltavar(ctx, t));
    int idx = t->var.idx;
    union term *d = get_bind(ctx, t->var.idx)->term;
    d = shift(d, idx+1, 0);
    t = subst(t, idx, 0, d);
    return t;
}

int isbetaradix(union term *t)
{
    return t->tag == tapp && t->app.fun->tag == tabs;
}

union term *beta(union term *t, jmp_buf jb)
{
    assert(isbetaradix(t));
    struct app *app = &t->app;
    struct abs *abs = &app->fun->abs;
    t = subst1(abs->exp, app->arg);
    free(abs);
    delete(app->arg);
    free(app);
    return t;
}

union term *full(struct ctx *ctx, union term *t, jmp_buf jb)
{
    switch (t->tag) {
    case tvar:
        if (isdeltavar(ctx, t)) {
            t = delta(ctx, t, jb);
            t = full(ctx, t, jb);
        }
        return t;
    case tabs:
        {
            struct abs *abs = &t->abs;
            abs->type = full(ctx, abs->type, jb);
            push_bind(ctx, abs->pos, abs->type, NULL);
            abs->exp = full(ctx, abs->exp, jb);
            pop_bind(ctx);
        }
        return t;
    case tprod:
        {
            struct prod *prod = &t->prod;
            prod->type = full(ctx, prod->type, jb);
            push_bind(ctx, prod->pos, prod->type, NULL);
            prod->exp = full(ctx, prod->exp, jb);
            pop_bind(ctx);
        }
        return t;
    case tapp:
        {
            struct app *app = &t->app;
            app->arg = full(ctx, app->arg, jb);
            app->fun = full(ctx, app->fun, jb);
            if (isbetaradix(t)) {
                t = beta(t, jb);
                t = full(ctx, t, jb);
            }
        }
        return t;
    case tuniv:
        return t;
    default:
        bug();
    }
}


int equal(union term *t1, union term *t2)
{
    if (t1->tag != t2->tag)
        return 0;
    switch (t1->tag) {
    case tvar:
        return t1->var.idx == t2->var.idx;
    case tuniv:
        return t1->univ.level == t2->univ.level;
    case tabs:
        if (!equal(t1->abs.type, t2->abs.type))
            return 0;
        if (!equal(t1->abs.exp, t2->abs.exp))
            return 0;
        return 1;
    case tprod:
        if (!equal(t1->prod.type, t2->prod.type))
            return 0;
        if (!equal(t1->prod.exp, t2->prod.exp))
            return 0;
        return 1;
    case tapp:
        if (!equal(t1->app.fun, t2->app.fun))
            return 0;
        if (!equal(t1->app.arg, t2->app.arg))
            return 0;
        return 1;
    default:
        bug();
    }
}

int fullequal(struct ctx *ctx, union term *t1, union term *t2)
{
    t1 = full(ctx, t1, NULL);
    t2 = full(ctx, t2, NULL);
    return equal(t1, t2);
}

int typeoftype(struct ctx *ctx, union term *t);
int type_check(struct ctx *ctx, union term *t, union term *etype);

union term *type_of(struct ctx *ctx, union term *t, jmp_buf jb)
{
    union term *type;
    switch (t->tag) {
    case tvar:
        {
            int idx = t->var.idx;
            type = copy(get_bind(ctx, idx)->type);
            type = shift(type, idx+1, 0);
        }
        return type;
    case tuniv:
        type = copy(t);
        type->univ.level+=1;
        return type;
    case tabs:
        {
            struct abs *abs = &t->abs;
            typeoftype(ctx, abs->type);
            push_bind(ctx, abs->pos, abs->type, NULL);
            union term *texp = type_of(ctx, abs->exp, NULL);
            pop_bind(ctx);
            type = malloc(sizeof(union term));
            type->prod.tag = tprod;
            type->prod.pos = abs->pos;
            type->prod.type = abs->type;
            type->prod.exp = texp;
        }
        return type;
    case tprod:
        {
            struct prod *prod = &t->prod;
            int utype = typeoftype(ctx, prod->type);
            push_bind(ctx, prod->pos, prod->type, NULL);
            int uexp = typeoftype(ctx, prod->exp);
            int umax = utype > uexp ? utype : uexp;
            type = malloc(sizeof(union term));
            type->univ.tag = tuniv;
            type->univ.pos = prod->pos;
            type->univ.level = umax;
        }
        return type;
    case tapp:
        {
            struct app *app = &t->app;
            union term *ftype = type_of(ctx, app->fun, NULL);
            if (ftype->tag != tprod)
                return NULL;
            struct prod *prod = &ftype->prod;
            if (!type_check(ctx, app->arg, prod->type))
                return NULL;
            push_bind(ctx, prod->pos, prod->type, app->arg);
            type = full(ctx, prod->exp, NULL);
            type = shift(type, -1, 0);
        }
        return type;
    default:
        bug();
    }
}

int typeoftype(struct ctx *ctx, union term *t)
{
    union term *type = type_of(ctx, t, NULL);
    type = full(ctx, type, NULL);
    if (type->tag != tuniv)
        error("not type of type!\n");
    return type->univ.level;
}

int type_check(struct ctx *ctx, union term *t, union term *etype)
{
    union term *type = type_of(ctx, t, NULL);
    if (type)
        return fullequal(ctx, type, etype);
    return 0;
}

FILE *read(FILE *src)
{
    FILE *tmp = tmpfile();
    int c;
    while ((c = fgetc(src)) !=  EOF)
        fputc(c, tmp);
    rewind(tmp);
    return tmp;
}

int main(int argc, char **argv)
{
    dbg = stderr;
    FILE *src = read(stdin);
    union term *term = parse(src);
    struct ctx ctx={0};
    term = full(&ctx, term, NULL);
    print(stdout, src, term);
    return 0;
}
