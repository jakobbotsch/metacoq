SED = `which gsed || which sed`

all: theory # plugin

Makefile.bd: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.bd $(DEPS)

theory: Makefile.bd
	$(MAKE) -f Makefile.bd

install: theory
	$(MAKE) -f Makefile.bd install

uninstall: theory
	$(MAKE) -f Makefile.bd uninstall

clean: Makefile.bd
	make -f Makefile.bd clean
