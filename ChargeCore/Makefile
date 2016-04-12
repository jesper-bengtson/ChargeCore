coq: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

dist:
	git archive --prefix=charge-core/ -o ChargeCore.tgz HEAD

install: coq
	$(MAKE) -f Makefile.coq install

_CoqProject: _CoqPath _CoqConfig Makefile
	@ echo "# Generating _CoqProject"
	@ rm -f _CoqProject
ifneq ("$(wildcard _CoqPath)","")
	@ echo "# including: _CoqPath"
	@ cp _CoqPath _CoqProject
	@ echo >> _CoqProject
endif
	@ echo "# including: _CoqConfig"
	@ cat _CoqConfig >> _CoqProject

_CoqPath:
	@ echo > /dev/null

.PHONY: all clean dist init coq
