#include <stdio.h>
#include <stdlib.h>
#include <setjmp.h>
#include <string.h>
#include <ctype.h>

FILE *dbg;
#define error(...) (fprintf(stderr, __VA_ARGS__), exit(1))
#define debug(...) (dbg && fprintf(dbg, __VA_ARGS__))

enum tag {
    _0, true, false,
    succ, pred, iszero,
    if_then_else,
};

struct term {
    enum tag tag;
    struct term *sub[3];
};

int match(FILE *in, char *str) {
    int c;
    fpos_t save;
    while(isspace(c = fgetc(in)));
    ungetc(c, in);
    fgetpos(in, &save);
    while (*str)
        if (fgetc(in) != *str++)
            goto mismatch;
    return !0;
mismatch:
    fsetpos(in, &save);
    return 0;
}

struct term *parse(FILE *in)
{
    struct term *t = malloc(sizeof(struct term));
    if (match(in, "0")) {
        t->tag = _0;
    } else if (match(in, "true")) {
        t->tag = true;
    } else if (match(in, "false")) {
        t->tag = false;
    } else if (match(in, "succ")) {
        t->tag = succ;
        t->sub[0] = parse(in);
    } else if (match(in, "pred")) {
        t->tag = pred;
        t->sub[0] = parse(in);
    } else if (match(in, "iszero")) {
        t->tag = iszero;
        t->sub[0] = parse(in);
    } else if (match(in, "if")) {
        t->tag = if_then_else;
        t->sub[0] = parse(in);
        if (!match(in, "then"))
            error("parse error\n");
        t->sub[1] = parse(in);
        if (!match(in, "else"))
            error("parse error\n");
        t->sub[2] = parse(in);
    } else if (match(in, "(")) {
        t = parse(in);
        if (!match(in, ")"))
            error("parse error\n");
    } else {
        error("parse error\n");
    }
    return t;
}

void print_term(FILE *out, struct term *t)
{
    switch (t->tag) {
    case _0:
        fputs("0", out);
        return;
    case true:
        fputs("true", out);
        return;
    case false:
        fputs("false", out);
        return;
        break;
    case iszero:
        fputs("iszero", out);
        fputs("(", out);
        print_term(out, t->sub[0]);
        fputs(")", out);
        return;
    case succ:
        fputs("succ", out);
        fputs("(", out);
        print_term(out, t->sub[0]);
        fputs(")", out);
        return;
    case pred:
        fputs("pred", out);
        fputs("(", out);
        print_term(out, t->sub[0]);
        fputs(")", out);
        return;
    case if_then_else:
        fputs("if ", out);
        print_term(out, t->sub[0]);
        fputs(" then ", out);
        print_term(out, t->sub[1]);
        fputs(" else ", out);
        print_term(out, t->sub[2]);
        return;
    }
    error("invalid term");
}

int print(FILE *out, struct term *t) {
    print_term(out, t);
    return fputs("\n", out);
}

int isnat(struct term *t)
{
    if (t->tag == _0)
        return !0;
    if (t->tag == succ && isnat(t->sub[0]))
        return !0;
    return 0;
}

struct term *eval1(struct term *t, jmp_buf ctx)
{
    struct term *tmp;
    switch (t->tag) {
    case if_then_else:
        switch (t->sub[0]->tag) {
        case true:
            debug(" -> E-IFTRUE");
            tmp = t->sub[1];
            free(t->sub[0]);
            free(t->sub[2]);
            free(t);
            return tmp;
        case false:
            debug(" -> E-IFFALSE");
            tmp = t->sub[2];
            free(t->sub[0]);
            free(t->sub[1]);
            free(t);
            return tmp;
        default:
            debug(" -> E-IF");
            t->sub[0] = eval1(t->sub[0], ctx);
            return t;
        }
    case succ:
        debug(" <- E-SUCC");
        t->sub[0] = eval1(t->sub[0], ctx);
        return t;
    case pred:
        switch (t->sub[0]->tag) {
        case _0:
            debug(" <- E-PREDZERO");
            free(t->sub[0]);
            t->tag = _0;
            return t;
        case succ:
            if (!isnat(t->sub[0]->sub[0]))
                longjmp(ctx, 1);
            debug(" <- E-PREDSUCC");
            tmp = t->sub[0]->sub[0];
            free(t->sub[0]);
            free(t);
            return tmp;
        default:
            debug(" <- E-PRED");
            t->sub[0] = eval1(t->sub[0], ctx);
            return t;
        }
    case iszero:
        switch (t->sub[0]->tag) {
        case _0:
            debug(" <- E-ISZEROZERO");
            free(t->sub[0]);
            t->tag = true;
            return t;
        case succ:
            debug(" <- E-ISZEROSUCC");
            free(t->sub[0]);
            t->tag = false;
            return t;
        default:
            debug(" <- E-ISZERO");
            t->sub[0] = eval1(t->sub[0], ctx);
            return t;
        }
    default:
        debug(" <- [no rule]\n");
        longjmp(ctx, 1);
    }
}

struct term *eval(struct term *t)
{
    jmp_buf ctx;
    while(!setjmp(ctx)) {
        dbg && print(dbg, t);
        t = eval1(t, ctx);
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
    struct term *t = parse(tmp);
    t = eval(t);
    print(stdout, t);
    return 0;
}
