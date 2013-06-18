
all:
	ocamlc -c deriving_Record.ml
	ocamlfind c -c -package camlp4.quotations.o,camlp4.fulllib,deriving-ocsigen -syntax camlp4o pa_deriving_Record.ml

clean:
	rm *.cmo *.cmi

install:
	ocamlfind install deriving-record META deriving_Record.cmi deriving_Record.cmo pa_deriving_Record.cmo

uninstall:
	ocamlfind remove deriving-record
