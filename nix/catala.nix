{ lib
, mkCoqDerivation
, coq-elpi
, autosubst
}:

mkCoqDerivation {
  pname = "catala";
  src = ../.;
  useDune = true;

  version = "0.1.0";

  propagatedBuildInputs = [
    autosubst
    (lib.overrideCoqDerivation {
      version="1.16.0";
      release."1.16.0".sha256="rGDzZUpaeJeWOXCeJ5ArdVG2FXlAnez/6X+Sz1xKiKM=";
    } coq-elpi)

  ];

  meta = {
    description = "Work in progress formalization for the Catala programming language";
  };
}
