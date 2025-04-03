{
  description = "Elan environment with direnv";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/24.11";

  outputs = { self, nixpkgs }:
    let pkgs = import nixpkgs { system = "x86_64-linux"; };
    in {
      devShell.x86_64-linux = pkgs.mkShell {
        buildInputs = [
          pkgs.elan
          pkgs.gcalcli
          pkgs.python312
        ]; # elanを使うようにしているだけだけど、なぜかelan経由でinstallしたlakeもstore objectになっていて、この環境だけ存在するようになっている
      };
    };
}
