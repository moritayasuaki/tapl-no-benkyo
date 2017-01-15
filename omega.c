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
#define error(...)  (fprintf(stderr, __VA_ARGS__), exit(EXIT_FAILURE))
#define debug(...)  (debug_file && fprintf(debug_file, __VA_ARGS__))
#define bug()       (error("%s:%d:%s() bug!\n", __FILE__, __LINE__, __func__))
#define LIM_ID_LEN  32
#define MIN_IDX     (INTPTR_MIN>>(CHAR_BIT*sizeof(intptr_t)/2))
#define MAX_IDX     (INTPTR_MAX>>(CHAR_BIT*sizeof(intptr_t)/2))

#define PROLOG      "+---------------+\n"\
                    "| TAPLE chap 4. |\n"\
                    "+---------------+\n"

#define EPILOG      "+---------------+\n"\
                    "|  good bye ;)  |\n"\
                    "+---------------+\n"

#define PROMPT      ">>> "
#define ANNOT       ":"
#define DOT         "."
#define ARROW       "->"
#define UNIV        "*"
#define LAMBDA      "fun"
#define FORALL      "forall"
#define DEFINE      "def"
#define DECLARE     "decl"
#define TYPEOF      "typeof"
#define BASIS       10

//#define LAMBDA      "lambda"
//#define FORALL      "forall"
//#define LAMBDA      u8"λ"
//#define FORALL      u8"∀"

FILE *debug_file;
int interactive;
int typeannotation;
union term;
struct bind;
fpos_t name;

typedef struct {intptr_t raw;} ref_t;
typedef struct {jmp_buf mem;} frm_t;

struct ctx {
    int len;
    struct bind *top;
    FILE *log;
    FILE *buf;
    FILE *src;
    FILE *dst;
    int un;
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
    ref_t (*parse)(struct ctx *);
    void (*print)(struct ctx *, ref_t);
    ref_t (*type)(struct ctx *, ref_t);
    ref_t (*eval)(struct ctx *, ref_t);
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
};

static_assert(tval < alignof(union term), "num of reference tag exceed pointer align\n");

#define is_nil(x)   (((x).raw) == 0)
#define nil         (ref_t){0}
#define univ(n)     (assert(n>0),(ref_t){n})
#define tsize       sizeof(union term)
#define talign      alignof(union term)

static inline intptr_t to_int(ref_t ref) {
    return ref.raw;
}

static inline void *to_ptr(ref_t ref) {
    return (void *)(ref.raw & -talign);
}

#define to_var(x)   to_int(x)
#define to_univ(x)  to_int(x)
#define to_abs(x)   ((struct abs *)to_ptr(x))
#define to_app(x)   ((struct app *)to_ptr(x))
#define to_arr(x)   ((struct arr *)to_ptr(x))

#define to_ref(x) generic((x),\
    struct abs*:    (ref_t){(intptr_t)(x) | tabs},\
    struct app*:    (ref_t){(intptr_t)(x) | tapp},\
    struct arr*:    (ref_t){(intptr_t)(x) | tarr},\
    struct val*:    (ref_t){(intptr_t)(x) | tval},\
    int:            (ref_t){(intptr_t)(x)},\
    default: (bug(),nil))

int is_var(ref_t ref) {
    return MIN_IDX <= ref.raw && ref.raw < 0;
}

int is_univ(ref_t ref) {
    return 0 < ref.raw && ref.raw <= MAX_IDX;
}

enum tag get_tag(ref_t ref)
{
    if (is_nil(ref))
        bug();
    if (is_univ(ref))
        return tuniv;
    if (is_var(ref))
        return tvar;
    return ref.raw & ~-talign;
}

int is_eof(FILE *f)
{
    return ferror(f) || feof(f);
}

int is_idhead(int c)
{
    return isalpha(c) || c == '_';
}

int is_idtail(int c)
{
    return isalnum(c) || c == '_';
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
            if (interactive)
                fputc('\0', ctx->buf);
            else
                fputc('\n', ctx->buf);
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

int emit(struct ctx *ctx, char *s)
{
    if (!*s)
        return 0;
    if (!isspace(ctx->un) && !isspace(*s))
        if (is_idtail(*s) && is_idtail(ctx->un))
            fputc(' ', ctx->dst);
    while (*s)
        fputc(*s++, ctx->dst);
    ctx->un = *(s-1);
    return *(s-1);
}

void skip_spaces(struct ctx *ctx)
{
    int c;
    do {
        c = eat_char(ctx);
    } while (isspace(c));
    undo_char(ctx, c);
}

int match_eos(struct ctx *ctx)
{
    int c;
    do {
        c = eat_char(ctx);
    } while (isspace(c));
    if (c == '\0')
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
    if (is_idtail(c))
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
    if (is_idhead(*s))
        return match_id(ctx, s);
    return match_str(ctx, s);
}


int is_keyword(char *id)
{
    static char const *keyword[] = {
        "in", "let", LAMBDA, FORALL, DEFINE, DECLARE, TYPEOF
    };
    int i = sizeof(keyword)/sizeof(*keyword);
    while (i--)
        if(!strcmp(id, keyword[i]))
            return 1;
    return 0;
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
    if (!is_idhead(c)) {
        undo_char(ctx, c);
        return EOF;
    }
    int l = 0;
    do {
        if (l < LIM_ID_LEN - 1)
            id[l] = c;
        c = eat_char(ctx);
        l++;
    } while (is_idtail(c));
    if (l >= LIM_ID_LEN) {
        warn("too long identifier\n");
        l = LIM_ID_LEN - 1;
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

#define try(ctx)    if(!setjmp((ctx)->frm.mem))
#define catch       else
#define throw(ctx)  longjmp((ctx)->frm.mem, 1)

ref_t discard(ref_t term);

ref_t parse_term(struct ctx *ctx);
ref_t parse_type(struct ctx *ctx);
ref_t parse_var(struct ctx *ctx);

#define parse_log(ctx, ...) (fprintf((ctx)->log, "%lld:",save_pos(ctx)), fprintf((ctx)->log, __VA_ARGS__))
#define print_log(ctx, ...) (fprintf((ctx)->log, __VA_ARGS__))

void reset_log(struct ctx *ctx)
{
    rewind(ctx->log);
}

#define debug_ctx(ctx, ...) (debug("%*s",(ctx)->len * 2, ""), debug(__VA_ARGS__))

int is_beta_redex(struct ctx *ctx, ref_t term);

fpos_t expect_id(struct ctx *ctx, char *id) {
    fpos_t pos = read_id(ctx, id);
    if (pos == EOF) {
        parse_log(ctx, "expected identifier\n");
        throw(ctx);
    }
    return pos;
}

void expect(struct ctx *ctx, char *tok) {
    if (!match(ctx, tok)) {
        parse_log(ctx, "expected '%s'\n", tok);
        throw(ctx);
    }
}
#define maybe(ctx, tok)\
    if (!match(ctx, tok)) return nil

ref_t parse_var(struct ctx *ctx)
{
    char id[LIM_ID_LEN];
    fpos_t pos = read_id(ctx, id);
    if (pos == EOF)
        return nil;
    debug_ctx(ctx, ">>%s\n", __func__);
    int idx = find_bind_idx(ctx, id);
    if (!idx) {
        restore_pos(ctx, pos);
        parse_log(ctx, "use of undeclared identifier '%s'\n", id);
        throw(ctx);
    }
    debug_ctx(ctx, "<<%s\n", __func__);
    return to_ref(idx);
}

ref_t parse_annot(struct ctx *ctx)
{
    fpos_t pos = save_pos(ctx);
    maybe(ctx, ANNOT);
    debug_ctx(ctx, ">>%s\n", __func__);
    ref_t type = parse_term(ctx);
    debug_ctx(ctx, "<<%s\n", __func__);
    return type;
}

ref_t parse_abs(struct ctx *ctx)
{
    frm_t frm = ctx->frm;
    ref_t type = nil;
    ref_t exp = nil;
    maybe(ctx, LAMBDA);
    try(ctx) {
        debug_ctx(ctx, ">>%s\n", __func__);
        char id[LIM_ID_LEN];
        fpos_t pos = expect_id(ctx, id);
        type = parse_annot(ctx);
        if (is_nil(type))
            type = univ(1);
        expect(ctx, DOT);
        push_bind(ctx, pos, type, nil);
        exp = parse_term(ctx);
        if (is_nil(exp))
            throw(ctx);
        struct abs *abs = malloc(tsize);
        abs->pos = pos;
        abs->exp = exp;
        abs->type = type;
        pop_bind(ctx);
        ctx->frm = frm;
        debug_ctx(ctx, "<<%s\n", __func__);
        return to_ref(abs);
    }
    discard(exp);
    discard(type);
    ctx->frm = frm;
    throw(ctx);
}

ref_t parse_all(struct ctx *ctx)
{
    frm_t frm = ctx->frm;
    ref_t src = nil;
    ref_t dst = nil;
    maybe(ctx, FORALL);
    try(ctx) {
        debug_ctx(ctx, ">>%s\n", __func__);
        char id[LIM_ID_LEN];
        fpos_t pos = expect_id(ctx, id);
        src = parse_annot(ctx);
        if (is_nil(src))
            src = univ(1);
        expect(ctx, DOT);
        push_bind(ctx, pos, src, nil);
        dst = parse_term(ctx);
        pop_bind(ctx);
        struct arr *arr = malloc(tsize);
        arr->src = src;
        arr->dst = dst;
        arr->pos = pos;
        debug_ctx(ctx, "<<%s\n", __func__);
        ctx->frm = frm;
        return to_ref(arr);
    }
    discard(src);
    discard(dst);
    ctx->frm = frm;
    throw(ctx);
}

ref_t parse_let(struct ctx *ctx)
{
    ref_t type = nil;
    ref_t sub = nil;
    ref_t exp = nil;
    frm_t frm = ctx->frm;
    maybe(ctx, "let");
    try(ctx) {
        debug_ctx(ctx, ">>%s\n", __func__);
        char id[LIM_ID_LEN];
        fpos_t pos = expect_id(ctx, id);
        type = parse_annot(ctx);
        expect(ctx, "=");
        sub = parse_term(ctx);
        if (is_nil(sub))
            throw(ctx);
        expect(ctx, "in");
        push_bind(ctx, pos, type, nil);
        exp = parse_term(ctx);
        pop_bind(ctx);
        struct app *app = malloc(tsize);
        struct abs *abs = malloc(tsize);
        abs->type = type;
        abs->exp = exp; 
        abs->pos = pos;
        app->fun = to_ref(abs);
        app->arg = sub;
        app->pos = pos;
        debug_ctx(ctx, "<<%s\n", __func__);
        ctx->frm = frm;
        return to_ref(app);
    }
    discard(type);
    discard(sub);
    discard(exp);
    ctx->frm = frm;
    throw(ctx);
}

ref_t parse_univ(struct ctx *ctx)
{
    maybe(ctx, UNIV);
    debug_ctx(ctx, ">>%s\n", __func__);
    int num = read_num(ctx);
    ref_t u;
    if (num <= 0)
        u = univ(1);
    else
        u = univ(num);
    debug_ctx(ctx, "<<%s\n", __func__);
    return u;
}

ref_t parse_num(struct ctx *ctx)
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

ref_t parse_fun(struct ctx *ctx)
{
    ref_t fun;
    if (match(ctx, "(")) {
        fun = parse_term(ctx);
        expect(ctx, ")");
        return fun;
    }
    fun = parse_let(ctx);
    if (!is_nil(fun))
        return fun;
    fun = parse_abs(ctx);
    if (!is_nil(fun))
        return fun;
    fun = parse_all(ctx);
    if (!is_nil(fun))
        return fun;
    fun = parse_univ(ctx);
    if (!is_nil(fun))
        return fun;
    fun = parse_var(ctx);
    if (!is_nil(fun))
        return fun;
    return nil;
}

ref_t parse_arr(struct ctx *ctx, ref_t type)
{
    maybe(ctx, ARROW);
    debug_ctx(ctx, ">>%s\n", __func__);
    push_bind(ctx, EOF, type, nil);
    ref_t dst = parse_term(ctx);
    pop_bind(ctx);
    if (is_nil(dst)) {
        discard(type);
        throw(ctx);
    }
    struct arr *arr = malloc(tsize);
    arr->src = type;
    arr->dst = dst;
    arr->pos = EOF;
    debug_ctx(ctx, "<<%s\n", __func__);
    return to_ref(arr);
}

ref_t parse_term(struct ctx *ctx)
{
    frm_t frm = ctx->frm;
    ref_t fun = parse_fun(ctx);
    if (is_nil(fun)) {
        parse_log(ctx, "expected expression\n");
        throw(ctx);
    }

    try(ctx) {
        ref_t arr = parse_arr(ctx, fun);
        if (!is_nil(arr)) {
            ctx->frm = frm;
            return arr;
        }
        while (1) {
            fpos_t pos = save_pos(ctx);
            debug_ctx(ctx, ">>%s\n", "parse_app");
            ref_t arg = parse_fun(ctx);
            if (is_nil(arg)) {
                debug_ctx(ctx, "fail %s\n", "parse_app");
                ctx->frm = frm;
                return fun;
            }
            struct app *app = malloc(tsize);
            app->fun = fun;
            app->arg = arg;
            app->pos = pos;
            fun = to_ref(app);
            debug_ctx(ctx, "<<%s\n", "parse_app");
        }
    }

    discard(fun);
    ctx->frm = frm;
    throw(ctx);
}

ref_t type_term(struct ctx *ctx, ref_t term);

ref_t parse(struct ctx *ctx)
{
    fpos_t pos = save_pos(ctx);
    fpos_t len = ctx->len;
    ref_t term = parse_term(ctx);
    if (interactive) {
        if (!match_eos(ctx)) {
            parse_log(ctx, "unneed character at end of line\n");
            throw(ctx);
        }
    } else {
        skip_spaces(ctx);
        if (!is_eof(ctx->buf)) {
            parse_log(ctx, "unneed character at end of file\n");
            throw(ctx);
        }
    }
    return term;
}

int print_term(struct ctx *ctx, ref_t term, int lapp);

int emit_id(struct ctx *ctx, fpos_t pos)
{
    char buf[LIM_ID_LEN];
    if (pos < 0) {
        int i = LIM_ID_LEN-1;
        buf[i] = '\0';
        while (pos < 0 && i) {
            buf[--i] = (-pos) % ('z' - 'a' + 1) + 'a';
            pos = pos/('z' - 'a' + 1);
        }
        return emit(ctx, &buf[i]);
    } else {
        fpos_t save = save_pos(ctx);
        restore_pos(ctx, pos);
        if (read_id(ctx, buf) == EOF)
            bug();
        restore_pos(ctx, save);
        return emit(ctx, buf);
    }
}

int to_digit(unsigned num)
{
    return "0123456789abcdef"[num];
}

int print_num(struct ctx *ctx, unsigned num)
{
    char buf[LIM_ID_LEN];
    int i = LIM_ID_LEN;
    buf[--i] = '\0';
    do {
        if (!i) {
            print_log(ctx, "too big number\n");
            throw(ctx);
        }
        buf[--i] = to_digit(num % BASIS);
        num /= BASIS;
    } while (num);
    return emit(ctx, &buf[i]);
}

int print_var(struct ctx *ctx, int idx)
{
    struct bind *bind = get_bind(ctx, idx);
    if (ctx->buf == NULL) {
        return print_num(ctx, -idx);
    }
    return emit_id(ctx, bind->pos);
}

int print_abs(struct ctx *ctx, struct abs *abs)
{
    emit(ctx, LAMBDA);
    if (ctx->buf)
        emit_id(ctx, abs->pos);
    emit(ctx, ANNOT);
    print_term(ctx, abs->type, 1);
    emit(ctx, ".");
    push_bind(ctx, abs->pos, abs->type, nil);
    int res = print_term(ctx, abs->exp, 0);
    pop_bind(ctx);
    return res;
}

int print_all(struct ctx *ctx, ref_t term) {
    struct arr *arr = to_arr(term);
    emit(ctx, FORALL);
    if (ctx->buf)
        emit_id(ctx, arr->pos);
    emit(ctx, ANNOT);
    print_term(ctx, arr->src, 1);
    emit(ctx, ".");
    push_bind(ctx, arr->pos, univ(1), nil);
    int res = print_term(ctx, arr->dst, 0);
    pop_bind(ctx);
    return res;
}

int print_arr(struct ctx *ctx, ref_t term) {
    struct arr *arr = to_arr(term);
    if (get_tag(arr->src) == tarr) {
        emit(ctx, "(");
        print_term(ctx, arr->src, 0);
        emit(ctx, ")");
    } else {
        print_term(ctx, arr->src, 0);
    }
    emit(ctx, ARROW);
    push_bind(ctx, EOF, arr->src, nil);
    int res = print_term(ctx, arr->dst, 0);
    pop_bind(ctx);
    return res;
}


int print_univ(struct ctx *ctx, int level)
{
    int res = emit(ctx, UNIV);
    if (level != 1)
        res = print_num(ctx, level);
    return res;
}

int print_let(struct ctx *ctx, ref_t term)
{
    struct app *app = to_app(term);
    struct abs *abs = to_abs(app->fun);
    emit(ctx, "let");
    if (ctx->buf)
        emit_id(ctx, abs->pos);
    if (!is_nil(abs->type)) {
        emit(ctx, ":");
        print_term(ctx, abs->type, 0);
    }
    emit(ctx, "=");
    print_term(ctx, app->arg, 0);
    emit(ctx, "in");
    push_bind(ctx, abs->pos, abs->type, app->arg);
    int res = print_term(ctx, abs->exp, 0);
    pop_bind(ctx);
    return res;
}

int print_term(struct ctx *ctx, ref_t term, int lapp)
{
    if (is_beta_redex(ctx, term))
        return print_let(ctx, term);
    switch (get_tag(term)) {
        struct app *app;
    case tvar:
        return print_var(ctx, to_var(term));
    case tabs:
        return print_abs(ctx, to_abs(term));
    case tapp:
        app = to_app(term);
        if (get_tag(app->fun) == tabs) {
            emit(ctx, "(");
            print_abs(ctx, to_abs(app->fun));
            emit(ctx, ")");
        } else if (get_tag(app->fun) == tvar) {
            print_var(ctx, to_var(app->fun));
        } else {
            print_term(ctx, app->fun, 1);
        }
        if (get_tag(app->arg) == tapp || (get_tag(app->arg) == tabs && lapp)) {
            emit(ctx, "(");
            print_term(ctx, app->arg, 0);
            return emit(ctx, ")");
        }
        return print_term(ctx, app->arg, 0);
    case tarr:
        if (to_arr(term)->pos == EOF)
            return print_arr(ctx, term);
        return print_all(ctx, term);
    case tuniv:
        return print_univ(ctx, to_univ(term));
    default:
        debug("%td\n", term.raw);
        bug();
    }
}

int print(struct ctx *ctx, ref_t term)
{
    print_term(ctx, term, 0);
    return emit(ctx, "\n");
}

int print_debug(struct ctx *ctx, ref_t term)
{
    if (!debug_file)
        return 0;
    FILE *dst = ctx->dst;
    int un = ctx->un;
    ctx->un = ' ';
    ctx->dst = debug_file;
    int ret = print(ctx, term);
    ctx->un = un;
    ctx->dst = dst;
    return ret;
}

int print_debug_idx(struct ctx *ctx, ref_t term)
{
    FILE *buf = ctx->buf;
    ctx->buf = NULL;
    int ret = print_debug(ctx, term);
    ctx->buf = buf;
    return ret;
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

ref_t discard(ref_t term)
{
    if (is_nil(term))
        return nil;
    switch (get_tag(term)) {
    case tvar:
        return nil;
    case tabs:
        discard(to_abs(term)->exp);
        discard(to_abs(term)->type);
        free(to_abs(term));
        return nil;
    case tapp:
        discard(to_app(term)->fun);
        discard(to_app(term)->arg);
        free(to_app(term));
        return nil;
    case tarr:
        discard(to_arr(term)->src);
        discard(to_arr(term)->dst);
        free(to_arr(term));
        return nil;
    case tuniv:
        return nil;
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

ref_t eval_beta(struct ctx *ctx, ref_t term)
{
    if (!is_beta_redex(ctx, term))
        throw(ctx);
    struct app *app = to_app(term);
    struct abs *abs = to_abs(app->fun);
    debug_ctx(ctx, ">>%s\n", __func__);
    app->arg = shift(app->arg, -1, 0);
    abs->exp = subst(abs->exp, -1, 0, app->arg);
    term = shift(abs->exp, 1, 0);
    free(abs);
    discard(app->arg);
    free(app);
    debug_ctx(ctx, "<<%s\n", __func__);
    return term;
}

int is_delta_redex(struct ctx *ctx, ref_t term)
{
    return get_tag(term) == tvar &&
        !is_nil(get_bind(ctx, to_var(term))->def);
}

ref_t eval_delta(struct ctx *ctx, ref_t term)
{
    if (!is_delta_redex(ctx, term))
        throw(ctx);
    int idx = to_var(term);
    struct bind *bind = get_bind(ctx, idx);
    debug_ctx(ctx, ">>%s\n", __func__);
    ref_t sub = copy(bind->def);
    sub = shift(sub, idx, 0);
    debug_ctx(ctx, "<<%s\n", __func__);
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

int type_eq(struct ctx *ctx, ref_t t0, ref_t t1)
{
    if (t0.raw == t1.raw)
        return 1;
    enum tag tag[2];
    tag[0] = get_tag(t0);
    tag[1] = get_tag(t1);
    for (int i = 0; i < 2; i++) {
        if (tag[i] == tabs) {
            type_log(ctx, to_abs(t0)->pos,  "abstraction is not allowed in type context\n");
            throw(ctx);
        }
        if (tag[i] == tapp) {
            type_log(ctx, to_abs(t0)->pos,  "application is not allowed in type context\n");
            throw(ctx);
        }
    }
    if (tag[0] != tag[1])
        return 0;
    switch (tag[0]) {
        struct arr *arr0;
        struct arr *arr1;
    case tvar:
        return 0;
    case tuniv:
        return 0;
    case tarr:
        arr0 = to_arr(t0);
        arr1 = to_arr(t1);
        return type_eq(ctx, arr0->src, arr1->src) &&
            type_eq(ctx, arr0->dst, arr1->dst);
    default:
        bug();
    }
}

ref_t type_term(struct ctx *ctx, ref_t term);

ref_t type_var(struct ctx *ctx, ref_t term)
{
    debug_ctx(ctx, ">>%s\n", __func__);
    int idx = to_var(term);
    ref_t tyvar = copy(get_bind(ctx, idx)->type);
    tyvar = shift(tyvar, idx, 0);
    debug_ctx(ctx, "<<%s\n", __func__);
    return tyvar;
}


ref_t type_abs(struct ctx *ctx, ref_t term)
{
    struct abs *abs = to_abs(term);
    debug_ctx(ctx, ">>%s\n", __func__);
    ref_t tyarg = abs->type;
    push_bind(ctx, abs->pos, tyarg, nil);
    ref_t tyexp = type_term(ctx, abs->exp);
    if (is_nil(tyexp)) {
        type_log(ctx, abs->pos, "type error\n");
        throw(ctx);
    }
    pop_bind(ctx);
    struct arr *arr = malloc(tsize);
    arr->src = tyarg;
    arr->dst = tyexp;
    arr->pos = abs->pos;
    debug_ctx(ctx, "<<%s\n", __func__);
    return to_ref(arr);
}

ref_t type_app(struct ctx *ctx, ref_t term)
{
    debug_ctx(ctx, ">>%s\n", __func__);
    struct app* app = to_app(term);
    ref_t tyfun = type_term(ctx, app->fun);
    if (is_nil(tyfun)) {
        type_log(ctx, app->pos, "function type check failed\n");
        throw(ctx);
    }
    ref_t tyarg = type_term(ctx, app->arg);
    if (is_nil(tyarg)) {
        type_log(ctx, app->pos, "parameter type check failed\n");
        throw(ctx);
    }
    if (get_tag(tyfun) != tarr) {
        type_log(ctx, app->pos, "expected arrow type\n");
        throw(ctx);
    }
    struct arr *arr = to_arr(tyfun);
    if (!type_eq(ctx, arr->src, tyarg)) {
        type_log(ctx, app->pos,  "parameter type mismatch\n");
        throw(ctx);
    }
    ref_t arg = copy(app->arg);
    ref_t type = copy(arr->dst);
    arg = shift(arg, -1, 0);
    type = subst(type, -1, 0, arg);
    type = shift(type, 1, 0);
    discard(arg);
    debug_ctx(ctx, "<<%s\n", __func__);
    return type;
}

ref_t type_let(struct ctx *ctx, ref_t term)
{
    struct app *app = to_app(term);
    struct abs *abs = to_abs(app->fun);
    debug_ctx(ctx, ">>%s\n", __func__);
    if (is_nil(abs->type)) {
        abs->type = type_term(ctx, app->arg);
    }
    debug_ctx(ctx, "<<%s\n", __func__);
    return type_app(ctx, term);
}

ref_t type_univ(struct ctx *ctx, ref_t term)
{
    return univ(to_univ(term)+1);
}

ref_t type_arr(struct ctx *ctx, ref_t term)
{
    return univ(1);
}

ref_t type_term(struct ctx *ctx, ref_t term)
{
    if (is_beta_redex(ctx, term))
        return type_let(ctx, term);
    switch (get_tag(term)) {
    case tvar:
        return type_var(ctx, term);
    case tabs:
        return type_abs(ctx, term);
    case tapp:
        return type_app(ctx, term);
    case tarr:
        return type_arr(ctx, term);
    case tuniv:
        return type_univ(ctx, term);
    default:
        bug();
    }
}

ref_t type(struct ctx *ctx, ref_t term)
{
    return type_term(ctx, term);
}

enum eval_order {
    eval_cbv,
    eval_cvn,
};

enum eval_goal {
    eval_weak_head_normal,
    eval_head_normal,
    eval_normal,
};

ref_t eval1(struct ctx *ctx, ref_t term)
{
    frm_t frm = ctx->frm;
    int len = ctx->len;
    try (ctx) {
        if (get_tag(term) != tapp)
            throw(ctx);
        struct app *app = to_app(term);
        app->fun = eval1(ctx, app->fun);
        ctx->frm = frm;
        return to_ref(app);
    } catch try (ctx) {
        if (get_tag(term) != tapp)
            throw(ctx);
        struct app *app = to_app(term);
        app->arg = eval1(ctx, app->arg);
        ctx->frm = frm;
        return to_ref(app);
    } catch try (ctx) {
        term = eval_beta(ctx, term);
        ctx->frm = frm;
        return term;
    } catch try (ctx) {
        term = eval_delta(ctx, term);
        ctx->frm = frm;
        return term;
    } catch try (ctx) {
        if (get_tag(term) != tabs)
            throw(ctx);
        struct abs *abs = to_abs(term);
        push_bind(ctx, abs->pos, abs->type, nil);
        abs->exp = eval1(ctx, abs->exp);
        pop_bind(ctx);
        ctx->frm = frm;
        return to_ref(abs);
    }
    ctx->len = len;
    ctx->frm = frm;
    throw(ctx);
}

ref_t eval(struct ctx *ctx, ref_t term)
{
    frm_t frm = ctx->frm;
    try(ctx) {
        while(1) {
            print_debug(ctx, term);
            term = eval1(ctx, term);
            debug("\n");
        }
    }
    debug("\n");
    ctx->frm = frm;
    return term;
}

void dump_log(struct ctx *ctx)
{
    fputc('\0', ctx->log);
    rewind(ctx->log);
    int c;
    while (1) {
        c = fgetc(ctx->log);
        if (c == EOF || c == '\0')
            break;
        fputc(c, stderr);
    }
    rewind(ctx->log);
}

struct ctx *define(struct ctx *ctx);
struct ctx *declare(struct ctx *ctx);
struct ctx *showtype(struct ctx *ctx);

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
    struct ctx base = {
        .len = 0,
        .src = stdin,
        .dst = stdout,
        .log = tmpfile(),
        .buf = tmpfile(),
        .top = NULL,
        .un = EOF
    };
    struct ctx *ctx = &base;
    if (interactive)
        info("%s", PROLOG);
    do {
        fpos_t pos = save_pos(ctx);
        int len = ctx->len;
        try(ctx) {
            if (is_eof(ctx->src)) {
                if (interactive)
                    info("%s", EPILOG);
                exit(EXIT_SUCCESS);
            }
            if (interactive)
                info("%s", PROMPT);
            read_line(ctx);
            if (define(ctx))
                continue;
            if (declare(ctx))
                continue;
            if (showtype(ctx))
                continue;
            debug("parse:\n");
            ref_t tm = parse(ctx); print_debug_idx(ctx, tm);
            print_debug(ctx, tm);
            debug("type:\n");
            ref_t ty = type(ctx, tm);
            print_debug_idx(ctx, ty);
            print_debug(ctx, ty);
            debug("eval:\n");
            tm = eval(ctx, tm);
            print_debug_idx(ctx, tm);
            debug("print:\n");
            print(ctx, tm);
        } catch {
            dump_log(ctx);
            if (!interactive)
                exit(EXIT_FAILURE);
            restore_pos(ctx, pos);
            ctx->len = len;
            ctx->un = EOF;
        }
    } while (interactive);
    exit(EXIT_FAILURE);
}

#define __expect_term(ctx, term) (is_nil(term)?(parse_log(ctx, "expected %s\n", #term), throw(ctx)):(void)0)
#define expect_term(ctx, term) __expect_term(ctx, term)

struct ctx *define(struct ctx *ctx)
{
    ref_t type = nil;
    ref_t def = nil;
    ref_t annot = nil;
    frm_t frm = ctx->frm;
    if (!match(ctx, DEFINE))
        return NULL;
    try(ctx) {
        char id[LIM_ID_LEN];
        fpos_t pos = expect_id(ctx, id);
        annot = parse_annot(ctx);
        expect(ctx, "=");
        def = parse_term(ctx);
        expect_term(ctx, def);
        ref_t type = type_term(ctx, def);
        expect_term(ctx, type);
        expect(ctx, ";");
        if (is_nil(annot))
            annot = copy(type);
        if (!type_eq(ctx, type, annot))
            throw(ctx);
        discard(annot);
        emit_id(ctx, pos);
        emit(ctx, ":");
        print_term(ctx, type, 0);
        emit(ctx, "\n");
        push_bind(ctx, pos, type, def);
        ctx->frm = frm;
        return ctx;
    }
    discard(annot);
    discard(type);
    discard(def);
    ctx->frm = frm;
    throw(ctx);
}

struct ctx *declare(struct ctx *ctx)
{
    ref_t decl = nil;
    frm_t frm = ctx->frm;
    if (!match(ctx, DECLARE))
        return NULL;
    try(ctx) {
        char id[LIM_ID_LEN];
        fpos_t pos = expect_id(ctx, id);
        decl = parse_annot(ctx);
        expect_term(ctx, decl);
        expect(ctx, ";");
        emit_id(ctx, pos);
        emit(ctx, ":");
        print(ctx, decl);
        push_bind(ctx, pos, decl, nil);
        ctx->frm = frm;
        return ctx;
    }
    discard(decl);
    ctx->frm = frm;
    throw(ctx);
}

struct ctx *showtype(struct ctx *ctx)
{
    ref_t ty = nil;
    ref_t tm = nil;
    frm_t frm = ctx->frm;
    if (!match(ctx, TYPEOF))
        return NULL;
    try(ctx) {
        tm = parse(ctx);
        ty = type(ctx, tm);
        print(ctx, ty);
    }
    discard(tm);
    discard(ty);
    ctx->frm = frm;
    throw(ctx);
}
