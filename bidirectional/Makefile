all: theory

#_CoqProject: _CoqProject.in metacoq-config
#	cat metacoq-config > _CoqProject
#	cat _CoqProject.in >> _CoqProject

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

mrproper:
	rm -f metacoq-config
	rm -f Makefile.bd _CoqProject

.merlin:
	make -f Makefile.bd .merlin
