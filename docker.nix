{ dockerTools, coqPackages, coq, dune_3, name, git, ocaml, gcc, busybox}:
dockerTools.buildLayeredImage {
  name = name;
  tag = "latest";
  contents = [ coq coqPackages.autosubst dune_3 git ocaml gcc busybox];
  fakeRootCommands = ''
    mkdir -p ./tmp
    chmod 1777 ./tmp
  '';


}
