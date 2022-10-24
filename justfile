
update:
  #!/usr/bin/env bash
  hash="$(gh api /repos/nixos/nixpkgs/commits \
     -H "Accept: application/vnd.github+json" \
     -X GET \
     -F page=1 \
     -F per_page=1 \
     -F sha=nixos-unstable \
     -F since=$(date -d 'last Thursday 00:00 UTC' +"%FT%T%Z") \
     -F until=$(date -d 'last Thursday 23:59 UTC' +"%FT%T%Z") \
     -q ".[0].sha")"
  if [[ -z "$hash" ]]; then
    echo "Fetching commit failed" 1>&2
    exit 1
  fi
  nix flake update --override-input nixpkgs nixpkgs/$hash

  echo "update flake $(date --iso-8601) with nixpkgs version of the $(date -d 'last Thursday 00:00 UTC' --iso-8601)"

build:
  #!/usr/bin/env bash
  dune build
