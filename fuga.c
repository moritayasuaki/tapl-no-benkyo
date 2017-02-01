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
#include <stdbool.h>

#define progname    "fuga"
#define version     "0.0.0"

#define lambda      (option.utf8?u8"λ":"lambda")
#define forall      (option.utf8?u8"∀":"forall")

#define generic     _Generic
#define info(...)   fprintf(stderr, __VA_ARGS__)
#define warn(...)   fprintf(stderr, __VA_ARGS__)
#define error(...)  (fprintf(stderr, __VA_ARGS__), exit(EXIT_FAILURE))
#define debug(...)  (env.dbg && fprintf(env.dbg, __VA_ARGS__))
#define bug()       (error("%s:%d:%s() bug!\n", __FILE__, __LINE__, __func__))
#define try         if (!setjmp(env.frm.mem))
#define catch       else
#define throw       longjmp(env.frm.mem, 1)
#define until(cnd)  while(!(cnd))
#define loop        while(1)
#define max(x,y)    ((x)>(y)?(x):(y))

typedef struct {
    jmp_buf mem;
} frm_t;

typedef struct {
    char *buf; int rp, wp;
} buf_t;

typedef struct {
    intptr_t raw;
} ref_t;

typedef struct bind {
    ref_t type, def;
    int pos;
} bind_t;

typedef struct arr {
    ref_t src /*[alignof(max_align_t)]*/ ;
    ref_t dst;
    int pos /*[alignof(max_align_t)]*/;
    int kind;
} arr_t;

typedef struct app {
    ref_t fun /*[alignof(max_align_t)]*/;
    ref_t arg;
} app_t;

union term {
    max_align_t align;
    arr_t arr;
    app_t app;
} term_t;

typedef enum tag {
    arr_e,
    app_e,
    var_e,
    univ_e,
} tag_t;

typedef struct env {
    int len;
    bind_t *ctx;
    FILE *dbg;
    FILE *src;
    FILE *dst;
    char *buf;
    int rp;
    int wp;
    int un;
    frm_t frm;
} env_t;

typedef struct option {
    bool interactive;
    bool verbose;
    bool utf8;
    char *prompt;
    char *filename;
} option_t;

static const ref_t nil = {0};

static ref_t univ(int n) {
    if (n <= 0)
        bug();
    return (ref_t){n};
}

static option_t option;
static env_t env;
static ref_t parse_term();
static int print_term(ref_t, int);
static ref_t type_term(ref_t);
static ref_t eval_term(ref_t);
static ref_t eval_term1(ref_t ref);

static intptr_t toint(ref_t ref) {
    return ref.raw;
}
static void *toptionr(ref_t ref) {
    return (void *)(ref.raw & -alignof(max_align_t));
}
static int tovar(ref_t x) {
    return toint(x);
}
static int touniv(ref_t x) {
    return toint(x);
}
static arr_t *toarr(ref_t ref) {
    return (arr_t *)toptionr(ref);
}
static app_t *toapp(ref_t ref) {
    return (app_t *)toptionr(ref);
}

#define toref(x) generic((x),\
    struct arr*:   (x)?(ref_t){(intptr_t)(x) | arr_e}:nil,\
    struct app*:    (x)?(ref_t){(intptr_t)(x) | app_e}:nil,\
    int:            (ref_t){(intptr_t)(x)},\
    default: (bug(),nil))

static bool isnil(ref_t ref) {
    return !ref.raw;
}
static bool isvar(ref_t ref) {
    return 0 > ref.raw && ref.raw >= INT_MIN;
}
static bool isuniv(ref_t ref) {
    return 0 < ref.raw && ref.raw <= INT_MAX;
}

static tag_t tag(ref_t ref) {
    if (isnil(ref))
        bug();
    if (isuniv(ref))
        return univ_e;
    if (isvar(ref))
        return var_e;
    return ref.raw & ~-alignof(max_align_t);
}

static bind_t *tobind(int var) {
    if (0 > var && env.len + var >= 0)
        return &env.ctx[env.len + var];
    bug();
}

static bool isarr(ref_t ref) {
    return tag(ref) == arr_e;
}

static bool isapp(ref_t ref) {
    return tag(ref) == app_e;
}

static int put_buf(int c) {
    env.buf = realloc(env.buf, env.wp + 1);
    env.buf[env.wp++] = c;
    return c; }

static int get_buf() {
    if (env.rp == env.wp)
        return EOF;
    int c = env.buf[env.rp++];
    return c;
}

static void fetch_line(void) {
    if (feof(env.src) || ferror(env.src))
        return;
    option.prompt && info("%s", option.prompt);
    int c;
    int comment = 0;
    do {
        c = fgetc(env.src);
        if (c == '#')
            comment = 1;
        if (c == EOF)
            return;
        put_buf(comment?' ':c);
    } while (c != '\n');
}


static int eat_char(void) {
    if (env.rp == env.wp)
        fetch_line();
    return get_buf();
}

static int undo_char(void) {
    if (!env.rp)
        return EOF;
    return --env.rp;
}

static int peek_char(void) {
    int c = eat_char();
    undo_char();
    return c;
}

static int emit_char(int c) {
    env.un = c;
    return fputc(c, env.dst);
}

static int emit_str(char *str) {
    if (!*str)
        return 0;
    if (isalnum(env.un) && isalnum(*str))
        emit_char(' ');
    while (*str)
        emit_char(*str++);
    return *--str;
}

static int emit_ident(int pos) {
    if (isalnum(env.un) && isalnum(env.buf[pos]))
        emit_char(' ');
    while (pos < env.wp) {
        int c = env.buf[pos];
        if (!isalnum(c))
            return 0;
        emit_char(c);
        pos++;
    }
    return 0;
}

typedef int pos_t;

static pos_t skip_spaces(void) {
    while (isspace(peek_char()))
        eat_char();
    return env.rp;
}


static int match_str(char *str) {
    int origin = env.rp;
    while (*str)
        if (eat_char() != *str++)
            return env.rp = origin, EOF;
    return origin;
}

static int match_ident(char *ident) {
    int origin = env.rp;
    if (match_str(ident) == EOF)
        return env.rp = origin, EOF;
    if (isalnum(peek_char()))
        return env.rp = origin, EOF;
    return origin;
}

static int match_token(char *tok) {
    skip_spaces();
    if (isalpha(*tok))
        return match_ident(tok);
    else
        return match_str(tok);
}

static int comp_ident(int pos0, int pos1) {
    char *p0 = env.buf + pos0;
    char *p1 = env.buf + pos1;
    while (isalnum(*p0)) {
        int d = *p0 - *p1;
        if (d)
            return d;
        p0++;
        p1++;
    }
    if (!isalnum(*p1))
        return 0;
    return *p0 - *p1;
}

static int find_bind(int pos)
{
    int origin = env.rp;
    for (int var = -1; env.len + var >= 0; var--) {
        if (comp_ident(env.ctx[env.len + var].pos, pos) == 0)
            return env.rp = origin, var;
    }
    return env.rp = origin, 0;
}

static void push_bind(int pos, ref_t type, ref_t def)
{
    bind_t *ctx = env.ctx;
    ctx = realloc(ctx, (env.len+1) * sizeof(bind_t));
    if (!ctx)
        error("no memory\n");
    ctx[env.len].pos = pos;
    ctx[env.len].type = type;
    ctx[env.len].def = def;
    env.ctx = ctx;
    env.len++;
}

static void back_bind(int len)
{
    if (env.len < len)
        bug();
    if (len)
        env.ctx = realloc(env.ctx, len * sizeof(bind_t));
    else
        free(env.ctx), env.ctx = NULL;
    env.len = len;
}

static void pop_bind(void)
{
    back_bind(env.len - 1);
}

static void discard(ref_t ref) {
    if (isnil(ref))
        return;
    switch(tag(ref)) {
    case var_e:
    case univ_e:
        return;
    case arr_e:
        {
            arr_t *arr = toarr(ref);
            discard(arr->src);
            discard(arr->dst);
            free(arr);
            return;
        }
    case app_e:
        {
            app_t *app = toapp(ref);
            discard(app->fun);
            discard(app->arg);
            free(app);
            return;
        }
    default:
        bug();
    }
}

static ref_t copy(ref_t ref) {
    switch (tag(ref)) {
    case var_e:
    case univ_e:
        return ref;
    case arr_e:
        {
            arr_t *arr = calloc(1, sizeof(term_t));
            memcpy(arr, toarr(ref), sizeof(term_t));
            arr->src = copy(toarr(ref)->src);
            arr->dst = copy(toarr(ref)->dst);
            return toref(arr);
        }
    case app_e:
        {
            app_t *app = calloc(1, sizeof(term_t));
            memcpy(app, toapp(ref), sizeof(term_t));
            app->fun = copy(toapp(ref)->fun);
            app->arg = copy(toapp(ref)->arg);
            return toref(app);
        }
    default:
        bug();
    }
}

static int count(ref_t ref, int j, int c) {
    switch (tag(ref)) {
    case var_e:
        return tovar(ref) == j+c;
    case univ_e:
        return 0;
    case arr_e:
        return count(toarr(ref)->src, j, c)
            +  count(toarr(ref)->dst, j, c - 1);
    case app_e:
        return count(toapp(ref)->fun, j, c)
            +  count(toapp(ref)->arg, j, c);
    default:
        bug();
    }
}

static ref_t shift(ref_t ref, int d, int c) {
    switch (tag(ref)) {
    case var_e:
        if (tovar(ref) < c)
            return toref(tovar(ref)+d);
        return ref;
    case univ_e:
        return ref;
    case arr_e:
        {
            arr_t *arr = toarr(ref);
            arr->src = shift(arr->src, d, c);
            arr->dst = shift(arr->dst, d, c - 1);
            return toref(arr);
        }
    case app_e:
        {
            app_t *app = toapp(ref);
            app->fun = shift(app->fun, d, c);
            app->arg = shift(app->arg, d, c);
            return toref(app);
        }
    default:
        bug();
    }
}

ref_t subst(ref_t ref, int j, int c, ref_t sub) {
    switch (tag(ref)) {
    case var_e:
        if (tovar(ref) == j+c) {
            sub = copy(sub);
            sub = shift(sub, c, 0);
            return sub;
        }
        return ref;
    case univ_e:
        return ref;
    case arr_e:
        {
            arr_t *arr = toarr(ref);
            arr->src = subst(arr->src, j, c, sub);
            arr->dst = subst(arr->dst, j, c - 1, sub);
            return toref(arr);
        }
    case app_e:
        {
            app_t *app = toapp(ref);
            app->fun = subst(app->fun, j, c, sub);
            app->arg = subst(app->arg, j, c, sub);
            return toref(app);
        }
    default:
        bug();
    }
}

int comp_term(ref_t t0, ref_t t1) {
    int diff;
    if (t0.raw == t1.raw)
        return 0;
    if ((diff = tag(t0) - tag(t1)))
        return diff;
    switch (tag(t0)) {
    case var_e:
    case univ_e:
        return 0;
    case arr_e:
        {
            arr_t *arr0 = toarr(t0);
            arr_t *arr1 = toarr(t1);
            if ((diff = comp_term(arr0->src, arr1->src)))
                return diff;
            if ((diff = comp_term(arr0->dst, arr1->dst)))
                return diff;
            return 0;
        }
    case app_e:
        {
            app_t *app0 = toapp(t0);
            app_t *app1 = toapp(t1);
            if ((diff = comp_term(app0->fun, app1->fun)))
                return diff;
            if ((diff = comp_term(app0->arg, app1->arg)))
                return diff;
            return 0;
        }
    default:
        bug();
    }
}

static int beta_redex(ref_t ref) {
    return isapp(ref) && isarr((toapp(ref)->fun)) && !toarr(toapp(ref)->fun)->kind;
}

static int delta_redex(ref_t ref) {
    return isvar(ref) && !isnil(tobind(tovar(ref))->def);
}

static int parse_ident(void) {
    int pos = skip_spaces();
    if (!isalpha(peek_char()))
        return EOF;
    eat_char();
    while (isalnum(peek_char()))
        eat_char();
    return pos;
}

static int match_keyword(void) {
    int pos = env.rp;
    if ( match_token("in") != EOF
        || match_token("let") != EOF
        || match_token(lambda) != EOF
        || match_token(forall) != EOF
       ) {
        return pos;
    }
    return EOF;
}

static ref_t parse_var(void) {
    int pos = env.rp;
    if (match_keyword() != EOF)
        return env.rp = pos, nil;
    pos = parse_ident();
    if (pos == EOF)
        return nil;
    int var = find_bind(pos);
    if (!var)
        debug("use of undeclared identfier\n"), throw;
    return toref(var);
}

static ref_t parse_annot(void) {
    if (match_token(":") == EOF)
        return nil;
    return parse_term();
}

static ref_t parse_arr(void) {
    int kind;
    if (match_token(lambda) != EOF)
        kind = 0;
    else if (match_token(forall) != EOF)
        kind = 1;
    else
        return nil;
    int pos;
    ref_t src = nil;
    ref_t dst = nil;
    frm_t frm = env.frm;
    int len = env.len;
    try {
        if ((pos = parse_ident()) == EOF)
            debug("%d:expected ident\n", env.rp), throw;
        if (isnil((src = parse_annot())))
            throw;
        if (match_token(".") == EOF)
            debug("%d:expected '.'\n", env.rp), throw;
        push_bind(pos, src, nil);
        if (isnil((dst = parse_term())))
            throw;
        arr_t *arr = calloc(1, sizeof(term_t));
        arr->src = src;
        arr->dst = dst;
        arr->pos = pos;
        arr->kind = kind;
        return back_bind(len), env.frm = frm, toref(arr);
    }
    discard(src);
    discard(dst);
    back_bind(len), env.frm = frm, throw;
}

static ref_t parse_let(void) {
    if (match_token("let") == EOF)
        return nil;
    int pos;
    ref_t src = nil;
    ref_t dst = nil;
    ref_t sub = nil;
    frm_t frm = env.frm;
    int len = env.len;
    try {
        if ((pos = parse_ident()) == EOF)
            warn("%d:expected ident\n", env.rp), throw;
        src = parse_annot();
        if (match_token("=") == EOF)
            warn("%d:expected '='\n", env.rp), throw;
        if (isnil((sub = parse_term())))
            throw;
        if (match_token("in") == EOF)
            warn("%d:expected 'in'\n", env.rp), throw;
        push_bind(pos, src, sub);
        if (isnil((dst = parse_term())))
            throw;
        app_t *app = calloc(1, sizeof(term_t));
        arr_t *arr = calloc(1, sizeof(term_t));
        arr->src = src;
        arr->dst = dst;
        arr->pos = pos;
        app->fun = toref(arr);
        app->arg = sub;
        return back_bind(len), env.frm = frm, toref(app);
    }
    discard(src);
    discard(dst);
    discard(sub);
    back_bind(len), env.frm = frm, throw;
}

static ref_t parse_univ(void) {
    int nat = 0;
    skip_spaces();
    while (match_str("*") != EOF)
        nat++;
    if (!nat)
        return nil;
    return univ(nat);
}

static ref_t parse_term1(void) {
    ref_t fun;
    if (match_token("(") != EOF) {
        if (isnil(fun = parse_term()))
            throw;
        if (match_token(")") == EOF)
            warn("%d:expected ')'\n", env.rp), throw;
        return fun;
    }
    if (!isnil(fun = parse_let()))
        return fun;
    if (!isnil(fun = parse_arr()))
        return fun;
    if (!isnil(fun = parse_univ()))
        return fun;
    if (!isnil(fun = parse_var()))
        return fun;
    return nil;
}

static ref_t parse_app(ref_t fun) {
    ref_t arg;
    int pos = skip_spaces();
    if (isnil((arg = parse_term1())))
        return nil;
    app_t *app = calloc(1, sizeof(term_t));
    app->fun = fun;
    app->arg = arg;
    return toref(app);
}

static ref_t parse_term(void) {
    ref_t fun = nil;
    frm_t frm = env.frm;
    if (isnil(fun = parse_term1()))
        throw;
    try loop {
        ref_t app;
        if (isnil((app = parse_app(fun))))
            return env.frm = frm, fun;
        fun = app;
    }
    discard(fun);
    env.frm = frm, throw;
}

static int print_num(int num) {
    if (!num)
        return 0;
    print_num(num/10);
    return emit_char('0' + num%10);
}

static int print_var(int var) {
    bind_t *bind = tobind(var);
    emit_ident(bind->pos);
    return 0;
}

static int print_annot(ref_t ref) {
    emit_str(":");
    print_term(ref, 0);
    return 0;
}

static int print_arr(arr_t *arr) {
    if (arr->kind) {
        if (!count(arr->dst, -1, 0)) {
            print_term(arr->src, 0);
            emit_str("->");
        } else {
            emit_str(forall);
            emit_ident(arr->pos);
            print_annot(arr->src);
            emit_str(".");
        }
    } else {
        emit_str(lambda);
        emit_ident(arr->pos);
        print_annot(arr->src);
        emit_str(".");
    }
    push_bind(arr->pos, arr->src, nil);
    print_term(arr->dst, 0);
    pop_bind();
    return 0;
}

static int print_univ(int univ) {
    while (univ--)
        emit_str("*");
    return 0;
}

static int print_let(ref_t ref) {
    app_t *app = toapp(ref);
    arr_t *arr = toarr(app->fun);
    emit_str("let");
    emit_ident(arr->pos);
    if (!isnil(arr->src))
        print_annot(arr->src);
    emit_str("=");
    print_term(app->arg, 0);
    emit_str("in");
    push_bind(arr->pos, arr->src, app->arg);
    print_term(arr->dst, 0);
    pop_bind();
    return 0;
}

int print_app(app_t *app) {
    print_term(app->fun, 11);
    print_term(app->arg, 12);
    return 0; 
}

static int print_term(ref_t ref, int pri) {
    if (beta_redex(ref))
        return print_let(ref);
    switch(tag(ref)) {
    case var_e:
        return print_var(tovar(ref));
    case univ_e:
        return print_univ(touniv(ref));
    case arr_e:
        if (pri > 0)
            emit_str("(");
        print_arr(toarr(ref));
        if (pri > 0)
            emit_str(")");
        return 0;
    case app_e:
        if (pri > 11)
            emit_str("(");
        print_app(toapp(ref));
        if (pri > 11)
            emit_str(")");
        return 0;
    default:
        bug();
    }
}

static ref_t type_var(int var) {
    ref_t type = copy(tobind(var)->type);
    return shift(type, var, 0);
}

static ref_t type_univ(int univ) {
    return toref(univ + 1);
}

static ref_t type_arr(arr_t *arr) {
    ref_t tsrc;
    ref_t tdst;
    if (isnil((tsrc = type_term(arr->src))))
        warn("%d:type error\n", arr->pos), throw;
    push_bind(arr->pos, arr->src, nil);
    if (isnil((tdst = type_term(arr->dst))))
        warn("%d:type error\n", arr->pos), throw;
    pop_bind();
    if (!arr->kind) {
        arr_t *tarr = calloc(1, sizeof(term_t));
        tarr->src = arr->src;
        tarr->dst = tdst;
        tarr->pos = arr->pos;
        tarr->kind = 1;
        return toref(tarr);
    } else {
        if (!isuniv(tsrc))
            throw;
        if (!isuniv(tdst))
            throw;
        return toref(max(touniv(tsrc)-1, touniv(tdst)));
    }
}

static ref_t type_app(app_t *app) {
    ref_t tfun, targ;
    if (isnil((tfun = type_term(app->fun))))
        warn("type error\n"), throw;
    if (!isarr(tfun))
        warn("function does not have array type\n"), throw;
    if (isnil((targ = type_term(app->arg))))
        warn("type error\n"), throw;
    arr_t *arr = toarr(tfun);
    if (comp_term(arr->src, targ) != 0)
        warn("%d:parameter type mismatch\n", arr->pos), throw;
    ref_t arg = copy(app->arg);
    ref_t type = arr->dst;
    arg = shift(arg, -1, 0);
    type = subst(arr->dst, -1, 0, arg);
    type = shift(arr->dst, 1, 0);
    discard(arg);
    discard(arr->src);
    free(arr);
    return type;
}

static ref_t type_let(ref_t let) {
    app_t *app = toapp(let);
    arr_t *arr = toarr(app->fun);
    if (isnil(arr->src))
        arr->src = type_term(app->arg);
    return type_app(app);
}

static ref_t type_term(ref_t ref) {
    if (beta_redex(ref))
        return type_let(ref);
    switch (tag(ref)) {
    case var_e:
        return type_var(tovar(ref));
    case univ_e:
        return type_univ(touniv(ref));
    case arr_e:
        return type_arr(toarr(ref));
    case app_e:
        return type_app(toapp(ref));
    default:
        bug();
    }
}


static ref_t eval_beta(ref_t ref) {
    if (!beta_redex(ref))
        return nil;
    app_t *app = toapp(ref);
    arr_t *arr = toarr(app->fun);
    app->arg = shift(app->arg, -1, 0);
    arr->dst = subst(arr->dst, -1, 0, app->arg);
    ref = shift(arr->dst, 1, 0);
    free(arr);
    discard(app->arg);
    free(app);
    return ref;
}

static ref_t eval_delta(ref_t ref) {
    if (!delta_redex(ref))
        return nil;
    int var = tovar(ref);
    bind_t *bind = tobind(var);
    ref_t sub = copy(bind->def);
    return shift(sub, var, 0);
}

static ref_t eval_fun(ref_t ref) {
    if (!isapp(ref))
        return nil;
    app_t *app = toapp(ref);
    app->fun = eval_term1(app->fun);
    return toref(app);
}

static ref_t eval_arg(ref_t ref) {
    if (!isapp(ref))
        return nil;
    app_t *app = toapp(ref);
    app->arg = eval_term1(app->arg);
    return toref(app);
}

static ref_t eval_arr(ref_t ref) {
    if (!isarr(ref))
        return nil;
    arr_t *arr = toarr(ref);
    if (arr->kind)
        return nil;
    push_bind(arr->pos, arr->src, nil);
    arr->dst = eval_term1(arr->dst);
    pop_bind();
    return toref(arr);
}

static ref_t eval_term1(ref_t ref) {
    ref_t res;
    if (!isnil((res = eval_beta(ref))))
        return res;
    if (!isnil((res = eval_delta(ref))))
        return res;
    if (!isnil((res = eval_fun(ref))))
        return res;
    if (!isnil((res = eval_arg(ref))))
        return res;
    if (!isnil((res = eval_arr(ref))))
        return res;
    throw;
}

static ref_t eval_term(ref_t ref) {
    frm_t frm = env.frm;
    int len = env.len;
    try loop
        ref = eval_term1(ref);
    env.frm = frm;
    back_bind(len);
    return ref;
}

static int show_prolog(void) {
    info(  "%s %s\n", progname, version);
    return 0;
}

static int show_epilog(void) {
    info(  "bye bye\n");
    return 0;
}

static int show_usage(void) {
    error(  "usage: dep [-ivu] [-p prompt] [file]\n");
}

#define option_flag(name) case *#name: {option.name = true; break;}
#define option_arg(name) case *#name: {target = &option.name; break;}

static int get_option(int argc, char **argv) {
    for (int i = 1; i < argc; i++) {
        if (argv[i][0] != '-') {
            option.filename = argv[i];
            continue;
        }
        for (int j = 1; argv[i][j]; j++) {
            char **target = NULL;
            switch (argv[i][j]) {
                option_flag(interactive);
                option_flag(verbose);
                option_flag(utf8);
                option_arg(prompt);
            default:
                warn(progname ":" "illegal option -- %c\n", argv[i][j]);
                show_usage();
            }
            if (target) {
                if (i >= argc) {
                    warn(progname ":" "option require an argument -- %c\n", argv[i][j]);
                    show_usage();
                } else {
                    *target = argv[++i];
                }
                break;
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    env.src = stdin;
    env.dst = stdout;
    env.dbg = NULL;
    get_option(argc, argv);
    if (option.filename)
        env.src = fopen(option.filename, "r");
    if (option.verbose)
        env.dbg = stderr;
    option.interactive && show_prolog();
    do {
        int wp = env.wp;
        int rp = env.rp;
        int len = env.len;
        ref_t term = nil;
        ref_t type = nil;
        try {
            debug("parse:\n");
            term = parse_term();
            if (match_token(";") == EOF)
                warn("%d:expected ';'\n", env.rp), throw;
            debug("type:\n");
            type = type_term(term);
            debug("eval:\n");
            term = eval_term(term);
            debug("print:\n");
            print_term(term, 0);
            print_annot(type);
            emit_str(";\n");
        } catch {
            discard(term);
            discard(type);
            env.wp = wp;
            env.rp = rp;
            back_bind(len);
        }
    } while (!ferror(env.src) && !feof(env.src));
    option.interactive && show_epilog();
    return ferror(env.src);
}





static int parse_numprefix(void) {
    int c = tolower(eat_char());
    if (!isdigit(c))
        return undo_char(), 0;
    if (c != '0')
        return undo_char(), 10;
    c = eat_char();
    if (c == 'x')
        return 0x10;
    if (c == 'b')
        return 2;
    return undo_char(), 010;
}

static int parse_number(int n, int b) {
    int c = tolower(eat_char());
    const char *d = "0123456789abcdef";
    const char *p = strchr(d, c);
    if (!p)
        return undo_char(), n;
    return parse_number(p - d + n * b, b);
}

