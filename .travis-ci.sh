# Edit this for your own project dependencies
OPAM_DEPENDS="ocamlfind ocamlbuild topkg camlp4 ctypes-foreign"

# install OCaml + OPAM
case "$OCAML_VERSION,$OPAM_VERSION" in
3.12.1,1.0.0) ppa=avsm/ocaml312+opam10 ;;
3.12.1,1.1.0) ppa=avsm/ocaml312+opam11 ;;
4.00.1,1.0.0) ppa=avsm/ocaml40+opam10 ;;
4.00.1,1.1.0) ppa=avsm/ocaml40+opam11 ;;
4.01.0,1.0.0) ppa=avsm/ocaml41+opam10 ;;
4.01.0,1.1.0) ppa=avsm/ocaml41+opam11 ;;
4.01.0,1.2.0) ppa=avsm/ocaml41+opam12 ;;
4.02.1,1.2.0) ppa=avsm/ocaml42+opam12 ;;
4.02.2,1.2.0) ppa=avsm/ocaml42+opam12 ;;
4.02.3,1.2.0) ppa=avsm/ocaml42+opam12 ;;
*) echo Unknown $OCAML_VERSION,$OPAM_VERSION; exit 1 ;;
esac
	 
echo "yes" | sudo add-apt-repository ppa:$ppa
sudo apt-get update -qq
sudo apt-get install -qq ocaml ocaml-native-compilers camlp4-extra opam
export OPAMYES=1
opam init 

eval `opam config env`

opam pin add -n hardcaml git://github.com/ujamjar/hardcaml
opam pin add -n sattools git://github.com/ujamjar/sattools

opam pin add -n $OPAMPKG -k git .
opam depext -y $DEPPKGS $OPAMPKG

opam install $DEPPKGS $OPAMPKG
