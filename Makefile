
all:
	ocamlc -c deriving_Record.ml
	ocamlfind c -c -package camlp4.quotations.o,camlp4.fulllib,deriving-ocsigen -syntax camlp4o pa_deriving_Record.ml


test:
	ocamlfind c -c -package deriving-ocsigen.syntax -syntax camlp4o -ppopt pa_deriving.cma -ppopt pa_deriving_Record.cmo test.ml

clean:
	rm *.cmo *.cmi

install:
	ocamlfind install deriving-record META deriving_Record.cmi deriving_Record.cmo pa_deriving_Record.cmo

uninstall:
	ocamlfind remove deriving-record

check:
	camlp4o `ocamlfind query -i-format deriving-ocsigen.syntax` pa_deriving.cma pa_deriving_Record.cmo -printer o test.ml
