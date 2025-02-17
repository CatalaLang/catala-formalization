{ dockerTools, coqPackages, coq, dune_3, name, busybox}:
dockerTools.buildLayeredImage {
  name = name;
  tag = "latest";
  contents = [ coq coqPackages.autosubst dune_3 busybox ];
}
