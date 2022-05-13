# Proofgold Lite

Proofgold Lite is a fork of the Proofgold Core software.
When run in server mode, it is a full node that also offers
extra services to other Proofgold Lite clients.

# proofgold

Proofgold is a cryptocurrency that rewards the best theorem provers.
Information about proofgold can be found at proofgold.org.

* System Requirements

Proofgold requires linux, curl, the ocaml programming language, the Zarith module
and litecoin.

On debian, installing the requirements (except Zarith) can be done as follows:

apt-get install build-essential ocaml curl libgmp-dev

Zarith is available here:

https://github.com/ocaml/Zarith

The README.md file explains how to compile and install Zarith.

Litecoin is available from litecoin.org. It needs to be run in a way
so that RPC calls can be made from Proofgold. This means the litecoin.conf
file needs to have some settings described below.

* Installation

```
./configure
make
```

Sometimes ocaml cannot find zarith. In that case, manually
edit Makefile (or Makefile.in and rerun ./configure)
to replace each occurrence of +zarith with the full path
to the directory where zarith was installed.

You can build the bytecode with either:

```
makebytecode
```

or

```
makevmbytecode
```

The second script compiles a version where ocaml
handles the threads instead of the operating system.
If you find proofgold is running very slowly,
you might need to use makevmbytecode to obtain
an executable that works as intended.

The configure script can be given some parameters.
For example, the default data directory is .proofgold in the
user's home directory. This can be changed as follows:

```
./configure -datadir=<fullpathtodir>
```

The configure script will create the data directory if it does not already exist.

* Configuration file

For proofgold to run properly, it needs to communicate with a litecoin daemon.

First set up your litecoin.conf file (in .litecoin) to contain the following lines:

```
txindex=1
server=1
rpcuser=litecoinrpcusername
rpcpassword=replacewithrealpassword
rpcallowip=127.0.0.1
```

where of course `replacewithrealpassword` should be replaced with a
serious password (to protect litecoins in your local wallet).
You should put some litecoins in a segwit address in the local wallet.

Now create a file `proofgold.conf` in your proofgold data directory.

```
ltcrpcuser=litecoinrpcusername
ltcrpcpass=replacewithrealpassword
ltcrpcport=9332
ltcaddress=yourltcsegwitaddress
```

There are many other configuration parameters you might want to set
in `proofgold.conf` (see `src/setconfig.ml`).  The ones above should suffice for proofgold
to interact with your litecoin node.

Here are a few examples of other configuration parameters.

If you want your node to listen for connections, give your IP and port
number by setting `ip=xx.xx.xx.xx` and `port=..`. The default port
number is 21805. There is no default IP address, and if none is given
then proofgold will not listen for incoming connections. You can have
proofgold listen for connections via a tor hidden service by setting
`onion=xxyouronionaddrxx.onion` `onionremoteport=..` and
`onionlocalport=..`.

Connections will only be created over tor (via socks proxies) if
`socks=4` is included in the configuration file.

After putting the proofgold/bin/ directory into your PATH,
proofgold can be run with a console interface as follows:

```
proofgold
```

For a full list of available commands use the command `help`.

Proofgold can also be run as a daemon using `proofgoldd`
and then RPC commands can be issued via `proofgoldcli`.

* Staking

Proofgold blocks are created by burning litecoins, possibly in
combination with staking proofgold currency (proofgold bars).  The
node will attempt to stake if `staking=1` is included in the
proofgold.conf file, or if -staking is included as a command line
argument.

Half of the block reward of a new block goes to the staker
and the other half is placed as a bounty on a pseudorandomly
generated proposition. Participants can claim the bounty
by proving the proposition or its negation.
