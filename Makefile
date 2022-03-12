THRS_DIR := 'theories'
SRC_DIRS := $(THRS_DIR) $(shell test -d 'vendor' && echo 'vendor')
ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")
# TEST_VFILES := $(shell find 'theories' -name "*Tests.v")
EXAMPLE_VFILES := $(shell find 'theories/examples' -name "*.v")
PROJ_VFILES := $(shell find 'theories' -name "*.v")
VFILES := $(filter-out $(EXAMPLE_VFILES),$(PROJ_VFILES))
COQARGS := "-w all"

default: $(VFILES:.v=.vo)
all: $(ALL_VFILES:.v=.vo)

_CoqProject:
	@echo "-Q theories HypVeri" > $@
	@echo "-Q vendor/machine_program_logic/theories machine_program_logic" >> $@;
	@echo "-Q vendor/machine_utils/theories machine_utils" >> $@;
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
	@time coqc -w none $(shell cat '_CoqProject') $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	@rm -f $(ALL_VFILES:.v=.vo) $(ALL_VFILES:.v=.glob) $(ALL_VFILES:.v=.vok) $(ALL_VFILES:.v=.vos)
	@find $(SRC_DIRS) -name ".*.aux" -exec rm {} \;
	rm -f _CoqProject .coqdeps.d

skip-qed: 
	./disable-qed.sh $(shell find $(THRS_DIR) -name "*.v")

ci: skip-qed

.PHONY: default all clean ci
.DELETE_ON_ERROR:
