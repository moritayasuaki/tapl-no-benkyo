# CFLAGS+=-DDEBUG -g
target = natbool let simplebool simplebool2 dependent lambda letint omega
testres = $(target:%=%.ok)
all: test build
build: $(target);
test: $(testres)

clean:
	rm -f $(target) $(testres)
%:%.c
	$(LINK.c) $< -o $@
%.ok:% %-test.sh
	./$*-test.sh
	touch $@

%.pdf:%.md
	pandoc $< -o $@

preview : README.pdf
	open $<
