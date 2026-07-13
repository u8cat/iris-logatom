all: build
.PHONY: all

build:
	@dune build --profile dev --display=short
.PHONY: build

# Build for the CI uses mangled names.
build-ci:
	@dune build --profile mangle --display=short --build-dir=_build_mangled
.PHONY: build-ci

clean:
	@dune clean
	@# Make sure not to enter the `_opam` folder.
	find [a-z]*/ \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -f Makefile.coq .lia.cache builddep/*
.PHONY: clean

# Install build-dependencies
OPAMFILES=$(wildcard *.opam)
BUILDDEPFILES=$(addsuffix -builddep.opam, $(addprefix builddep/,$(basename $(OPAMFILES))))

builddep/%-builddep.opam: %.opam Makefile
	@echo "# Creating builddep package for $<."
	@mkdir -p builddep
	@sed <$< -E 's/^(build|install|remove):.*/\1: []/; s/"(.*)"(.*= *version.*)$$/"\1-builddep"\2/;' >$@

builddep-opamfiles: $(BUILDDEPFILES)
.PHONY: builddep-opamfiles

builddep: builddep-opamfiles
	@# We want opam to not just install the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything itself.
	@echo "# Installing builddep packages."
	@opam install $(OPAMFLAGS) $(BUILDDEPFILES)
.PHONY: builddep

# Backwards compatibility target
build-dep: builddep
.PHONY: build-dep

builddep-clean:
	@rm -f Makefile.coq .lia.cache builddep/*
.PHONY: builddep-clean
