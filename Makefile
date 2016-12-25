target = nb lam
all: $(target)
test: $(target:%=%-test)
clean:; rm -f $(target)
%:%.c
	cc $< -o $@

%-test :%
	./$@.sh
