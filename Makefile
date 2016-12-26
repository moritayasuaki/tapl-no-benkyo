CPPFLAGS+=-DNDEBUG
target = nb lam
test = nb-test lam-test
all: $(target) $(test)
clean:
	rm -f $(target) $(test)
%-test:
	./$@.sh
