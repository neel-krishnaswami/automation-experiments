AGDA = agda
MAIN = unification.agda
SOURCES = $(wildcard *.agda)

.PHONY: all check clean

all: check

check: $(SOURCES)
	$(AGDA) $(MAIN)

clean:
	rm -rf _build
