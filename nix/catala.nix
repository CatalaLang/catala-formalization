{ lib
, mkCoqDerivation
, coq
, autosubst
}:

mkCoqDerivation {
  pname = "catala";
  src = ../.;
  useDune = true;

  version = "0.1.0";

  propagatedBuildInputs = [
    autosubst
  ];

  meta = {
    description = "Work in progress formalization for the Catala programming language";
  };
}
