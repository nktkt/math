.PHONY: verify papers

verify:
	lake exe cache get Mathlib.Data.Fintype.Pi Mathlib.Data.Rat.Defs \
	  Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Data.Fintype.BigOperators \
	  Mathlib.Data.Fintype.Powerset Mathlib.Data.Nat.Choose.Cast Mathlib.Tactic.Ring
	lake --wfail build
	lake env lean PaperCheck.lean
	lake env leanchecker --fresh --verbose MatharThreeColumns

papers:
	mkdir -p build/paper output/pdf
	cd paper && SOURCE_DATE_EPOCH=1795564800 FORCE_SOURCE_DATE=1 \
	  latexmk -norc -lualatex -interaction=nonstopmode -halt-on-error \
	  -outdir=../build/paper three-columns.tex three-columns-ja.tex
	cp build/paper/three-columns.pdf build/paper/three-columns-ja.pdf output/pdf/
