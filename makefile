OCAMLPREFIX=
OCAMLC=         $(OCAMLPREFIX)ocamlc
OCAMLOPT=       $(OCAMLPREFIX)ocamlopt.opt
OCAMLYACC=      $(OCAMLPREFIX)ocamlyacc -v
OCAMLLEX=       $(OCAMLPREFIX)ocamllex
OCAMLDEP=       $(OCAMLPREFIX)ocamldep
OCAMLINCLUDES=
OCAMLFLAGS=     -warn-error a $(OCAMLINCLUDES)
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
ML_FILES=	simple_C_syntax.ml \
		utils.ml \
		offset.ml \
		domain_sig.ml \
		inductive_def.ml \
		neq_pred_domain.ml \
		SL_graph_domain.ml \
		SL_domain.ml \
		SL_Functor_domain.ml		
CMX_FILES=      $(ML_FILES:%.ml=%.cmx)
analyzer: $(CMX_FILES) 
	ocamlopt $(CMX_FILES) -o analyzer
clean: 
	rm -f *.cmi *.cmx *.o && \
	rm -f analyzer depend *~ debug.log \


