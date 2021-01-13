DESIGNS := $(shell cat tests.txt)

.PHONY: ${DESIGNS} all clean

all: ${DESIGNS}

$(DESIGNS):
	make -C $@ all -j$(nproc)

clean:
	for dir in $(DESIGNS); do \
	  make -C $$dir clean;    \
	done
