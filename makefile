OCAMLPREFIX=
OCAMLC=         $(OCAMLPREFIX)ocamlc
OCAMLOPT=       $(OCAMLPREFIX)ocamlopt.opt
OCAMLYACC=      $(OCAMLPREFIX)ocamlyacc -v
OCAMLLEX=       $(OCAMLPREFIX)ocamllex
OCAMLDEP=       $(OCAMLPREFIX)ocamldep
OCAMLINCLUDES=
OCAMLFLAGS=     -warn-error a $(OCAMLINCLUDES)
OCAMLC=         $(OCAMLPREFIX)ocamlc
OCAMLOPT=       $(OCAMLPREFIX)ocamlopt.opt
%.ml: %.mll
	$(OCAMLLEX) $*.mll
%.ml %.mli: %.mly
	$(OCAMLYACC) $*.mly
%.cmo: %.ml %.cmi
	$(OCAMLC) $(OCAMLFLAGS) -c $*.ml
%.cmx: %.ml %.cmi
	$(OCAMLOPT) $(OCAMLFLAGS) -c $*.ml
%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) -c $*.mli
%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -c $*.ml
%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLFLAGS) -c $*.ml
all: analyzer
AUTOGEN_ML=	
AUTOGEN_MLI=    
AUTOGEN= $(AUTOGEN_ML) $(AUTOGEN_MLI)
ML_FILES=	simple_C_syntax.ml \
		utils.ml \
		offset.ml \
		domain_sig.ml \
		concrete_domain.ml \
		TVLA_domain.ml \
		SL_domain.ml \
		environment.ml 		
CMO_FILES=	$(ML_FILES:%.ml=%.cmo)
CMX_FILES=      $(ML_FILES:%.ml=%.cmx)
analyzer: $(CMX_FILES) $(AUTOGEN)
	ocamlopt $(CMX_FILES) -o analyzer

depend: $(AUTOGEN_ML) $(ML_FILES)
	ocamldep $(OCAMLINCLUDES) *.mli *.ml */*.mli */*.ml > depend
clean: 
	rm -f *.cmo *.cmi *.cmx */*.cmi */*.cmo */*.cmx && \
	rm -f *.o $(AUTOGEN_ML) $(AUTOGEN_MLI) analyzer depend *~ \
	rm -r *.output
include depend
