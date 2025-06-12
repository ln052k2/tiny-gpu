VLIB      := vlib
VLOG      := vlog

LIB1      := gpu
LIB2      := base
WORK      := work

SRC_DIR       := src
SRC_BASELINE_DIR   := src_variant
TEST_DIR      := test

MAIN_SRCS     := $(shell cat buildorder/main.f)
BASELINE_SRCS     := $(shell cat buildorder/baseline.f)
TEST_SRCS     := $(shell cat buildorder/tests.f)

.PHONY: all clean

depend all: clean $(LIB1) $(LIB2) $(WORK)
	@echo "Finished building!"

$(LIB1):
	@echo ">> Building $(LIB1)..."
	$(VLIB) $(LIB1)
	$(VLOG) -quiet -work $(LIB1) $(MAIN_SRCS)

$(LIB2):
	@echo ">> Building $(LIB2)..."
	$(VLIB) $(LIB2)
	$(VLOG) -quiet -work $(LIB2) $(BASELINE_SRCS)

$(WORK):
	@echo ">> Building $(WORK)..."
	$(VLIB) $(WORK)
	$(VLOG) -quiet -work $(WORK) -L $(LIB1) -L $(LIB2) $(TEST_SRCS)

clean:
	@echo ">> Cleaning up..."
	rm -rf $(LIB1) $(LIB2) $(WORK) transcript vsim.wlf

