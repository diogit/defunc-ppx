# Nome de ficheiros
BEFORE = Before/height
AFTER = After/defunc_height

# Comandos
clean = rm -r -f *.native $(RESULT)*
before = ocamlopt -o $(BEFORE) unix.cmxa $(BEFORE).ml  && ./$(BEFORE)
after = ocamlopt -o $(AFTER) unix.cmxa $(AFTER).ml  && ./$(AFTER)

all:
	$(before)
	$(after)

h: 
	$(before)
deh:
	$(after)


