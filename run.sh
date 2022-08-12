
rm -rf ./typesetting || echo 1;
mkdir typesetting || echo 1;
cd typesetting;
rm *;

cp ../preamble.sty .;
cp ../coqdoc.sty .;
cp ../SFMono-Regular.otf .;
cp ../SF-Mono-Semibold.otf .;

coqdoc --latex --preamble "$(cat preamble.tex)" ../SemanticEquivelence.v -o SemanticEquivelence_proofs.tex
coqdoc --pdf --preamble "$(cat preamble.tex)"   ../SemanticEquivelence.v -o SemanticEquivelence_proofs.pdf 
coqdoc -g --pdf --preamble "$(cat preamble.tex)"  ../SemanticEquivelence.v -o SemanticEquivelence.pdf

rm ./coqdoc.sty;
rm ./preamble.sty;

cp ../preamble.sty .;
cp ../coqdoc.sty .;


cd ..;