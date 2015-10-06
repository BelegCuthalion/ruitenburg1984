echo "Compiling the IPC file ... "
coqc HilbertIPCsetup
echo "Compiling the Ruitenburg1984Aux file ..."
coqc Ruitenburg1984Aux
echo "Compiling the BoundsSubformulas file ..."
coqc BoundsSubformulas
echo "Compiling the KeyTheorem file ..."
coqc Ruitenburg1984KeyTheorem
echo "Compiling the Ruitenburg1984Main file ..."
coqc Ruitenburg1984Main
echo "succeeded? Then generate coqdoc documentation"
coqdoc -g HilbertIPCsetup.v Ruitenburg1984Aux.v BoundsSubformulas.v Ruitenburg1984KeyTheorem.v Ruitenburg1984Main.v
