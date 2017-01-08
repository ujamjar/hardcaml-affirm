.PHONY: all build examples clean

all: build

build:
	ocaml pkg/pkg.ml build

examples:
	ocamlbuild examples.otarget

clean:
	ocaml pkg/pkg.ml clean
	find . -name "*~" | xargs rm -f
	rm -f *.bc *.ll

