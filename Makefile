#CFLAGS+=-DDEBUG
target = nb lam
testres = $(target:%=%.ok)
all: test build
build: $(target);
test: $(testres)

clean:
	rm -f $(target) $(testres)
%:%.c
	$(LINK.c) $< -o $@
%.ok:% %.test
	./$*.test && touch $@
