CPPFLAGS+=-DNDEBUG
target = nb lam
test = $(target:%=%-test)
all: $(target) $(test)
clean:
	rm -f $(target) $(test)
%-test: % %-test.sh
	./$@.sh && touch $@
