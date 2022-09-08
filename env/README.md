# Environment Setup

## Jasmin

After cloning this repository and perhaps running `git submodule init` there should be a `jasmin` directory.

To build the Jasmin compiler, usually the following sequence of commands work (mostly tested on linux* machines):

1. `nix-shell`

Checkout the `https://nixos.org/download.html` where you can find something of the sort:

```
sh <(curl -L https://nixos.org/nix/install) --daemon
```

2. `jasmin/compiler/jasminc`

```
cd jasmin
nix-shell # this might take some time the first time it runs
cd compiler/
make CIL
make
```

3. `eclib`

If you already have EasyCrypt installed, there should be a `easycrypt.conf` file on directory `/home/\`whoami\`/.config/easycrypt`. It should contain the following entry:

```
[general]
idirs = Jasmin:/home/USER/jasmin-zk/jasmin/eclib
```
