target = nb lam
all: $(target)
clean:; rm -f $(target)
%:%.c
	cc $< -o $@
