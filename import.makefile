-include .env
# Variables
DEST_DIR := build
SRC_DIR := $(GEOCOQ_PATH)/Elements/OriginalProofs
LEMMA_FILES := $(wildcard $(SRC_DIR)/lemma_*.v)
PROPOSITION_FILES := $(wildcard $(SRC_DIR)/proposition_*.v)
TXT_FILES := $(LEMMA_FILES) $(PROPOSITION_FILES)
OUT_FILES := $(patsubst $(SRC_DIR)/%.v,$(DEST_DIR)/%_parse_tree.json,$(TXT_FILES))
CMD := rosie -f geocoq.rpl grep -o jsonpp -w top

# Targets
.PHONY: all copy_files process_files

all: copy_files process_files

copy_files:
	mkdir -p $(DEST_DIR)
	echo $(TXT_FILES)
	cp $(TXT_FILES) $(DEST_DIR)

process_files: $(OUT_FILES)

$(DEST_DIR)/%_parse_tree.json: $(DEST_DIR)/%.v
	sed -i -E -f sed_renames.txt $<
	$(CMD) $< > $@
