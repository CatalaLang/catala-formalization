{ dockerTools, coqPackages, coq, dune_3, github-runner, name}:
dockerTools.buildLayeredImage {
  name = name;
  tag = "latest";
  contents = [ coq coqPackages.autosubst dune_3 github-runner ];
}
