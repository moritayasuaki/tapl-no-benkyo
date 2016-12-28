#CFLAGS+=-DDEBUG
target = natbool lambda
testres = $(target:%=%.ok)
all: test build
build: $(target);
test: $(testres)

clean:
	rm -f $(target) $(testres)
%:%.c
	$(LINK.c) $< -o $@
%.ok:% %-test.sh
	./$*-test.sh && touch $@
