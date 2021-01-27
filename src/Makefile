
all:
	agda -v 2 Main.agda

docs:
	agda --html --html-dir=../docs Main.agda

diff:
	for i in *.agda; do diff $$i ../Mono/$$i; done

vim:
	for i in *.agda; do \
		vimdiff $$i ../Mono/$$i; \
		echo "Press ENTER to continue, CTRL-C to quit..."; \
		read; \
	done

%.diff:
	vimdiff $(@:%.diff=%) ../Mono/$(@:%.diff=%)
