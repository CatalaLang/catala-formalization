{ dockerTools, coqPackages, coq, dune_3, name, git, ocaml, gcc, busybox}:


dockerTools.buildLayeredImage {
  name = name;
  tag = "latest";
  contents = [ coq coqPackages.autosubst dune_3 git ocaml gcc busybox];

  extraCommands = ''
    mkdir -m 1777 tmp

    # mkdir -p /lib/coq/user-contrib/
    # mkdir -p /lib/coq/8.20/user-contrib/Autosubst

    # ln -s /lib/coq/8.20/user-contrib/Autosubst /lib/coq/user-contrib/
  '';



  config = {
    Cmd = [ "/bin/dune" "build" ];
    WorkingDir = "/app";
    Env = [
      "COQLIB=/lib/coq"
      "COQCORELIB=/lib/coq-core"
      "COQPATH=/lib/coq/user-contrib"
    ];
  };
}
