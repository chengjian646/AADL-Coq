SED := sed
CAT := cat
AWK := awk
COQC := coqc
OCAMLOPT := ocamlopt
COQMAKEFILE := coq_makefile
CP := cp
MV := mv

COQEXTRAFLAGS := COQEXTRAFLAGS = '-w all,-extraction,-disj-pattern-notation'

# 自动获取所有 Coq 文件
SRC = $(shell find src/static -name "*.v")

COQSRC = $(SRC)

all:
	@echo $@
	@$(MAKE) src

src:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQSRC) $(COQEXTRAFLAGS) -o CoqMakefile
	make -f CoqMakefile

clean:
	@echo $@
	make -f CoqMakefile clean
	find . -name "*\.vo" -exec rm {} \;
	find . -name "*\.vok" -exec rm {} \;
	find . -name "*\.vos" -exec rm {} \;
	find . -name "*\.glob" -exec rm {} \;
	find . -name "*\.aux" -exec rm {} \;
	find . -name "*\.cmi" -exec rm {} \;
	find . -name "*\.cmx" -exec rm {} \;
	find . -name "*\.crashcoqide" -exec rm {} \;

.SECONDARY:

.PHONY: all src clean

