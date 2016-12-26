CPPFLAGS+=-DNDEBUG
target = nb lam
all: $(target) test
test: $(target:%=%-test)
clean:
	rm -f $(target)
%-test:%
	./$@.sh
