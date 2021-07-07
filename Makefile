SRC_DIRS := 'theories' $(shell test -d 'vendor' && echo 'vendor')
ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")
TEST_VFILES := $(shell find 'theories' -name "*Tests.v")
PROJ_VFILES := $(shell find 'theories' -name "*.v")
VFILES := $(filter-out $(TEST_VFILES),$(PROJ_VFILES))

COQARGS := "-w all"

default: $(VFILES:.v=.vo)
test: $(TEST_VFILES:.v=.vo) $(VFILES:.v=.vo)

_CoqProject:
	@echo "-R theories HypVeri" > $@
	@echo "-R vendor/machine_program_logic/theories machine_program_logic" >> $@;
	@echo "-R vendor/machine_utils/theories machine_utils" >> $@;
	@echo "_CoqProject:"
	@cat $@

.coqdeps.d: $(ALL_VFILES) _CoqProject
	@echo "COQDEP $@"
	@coqdep -f _CoqProject $(ALL_VFILES) > $@

ifneq ($(MAKECMDGOALS), clean)
-include .coqdeps.d
endif

%.vo: %.v _CoqProject
	@echo "COQC $<"
	@coqc -w none $(shell cat '_CoqProject') $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	@rm -f $(ALL_VFILES:.v=.vo) $(ALL_VFILES:.v=.glob)
	@find $(SRC_DIRS) -name ".*.aux" -exec rm {} \;
	rm -f _CoqProject .coqdeps.d

.PHONY: default test clean
.DELETE_ON_ERROR:
