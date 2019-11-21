#!/bin/bash
# -------------------------------------------------------------------------------------------------
#
#    ,ggggggggggg,     _,gggggg,_      ,ggggggggggg,      ,gggg,  
#   dP"""88""""""Y8, ,d8P""d8P"Y8b,   dP"""88""""""Y8,  ,88"""Y8b,
#   Yb,  88      `8b,d8'   Y8   "8b,dPYb,  88      `8b d8"     `Y8
#    `"  88      ,8Pd8'    `Ybaaad88P' `"  88      ,8Pd8'   8b  d8
#        88aaaad8P" 8P       `""""Y8       88aaaad8P",8I    "Y88P'
#        88""""Y8ba 8b            d8       88"""""   I8'          
#        88      `8bY8,          ,8P       88        d8           
#        88      ,8P`Y8,        ,8P'       88        Y8,          
#        88_____,d8' `Y8b,,__,,d8P'        88        `Yba,,_____, 
#       88888888P"     `"Y8888P"'          88          `"Y8888888 
#
#   The Block Oriented Programming (BOP) Compiler - v2.1
#
#
# Kyriakos Ispoglou (ispo) - ispo@purdue.edu
# PURDUE University, Fall 2016-18
# -------------------------------------------------------------------------------------------------
msg() {
    GREEN='\033[01;32m'                         # bold green
    NC='\033[0m'                                # no color
    echo -e "${GREEN}[INFO]${NC} $1"
}

error() {
    RED='\033[01;31m'                           # bold red
    NC='\033[0m'                                # no color
    echo -e "${RED}[ERROR]${NC} $1"
}


# display fancy foo
clear
echo
echo -e '\t%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'
echo -e '\t%                                                                    %'
echo -e '\t%                :::::::::   ::::::::  :::::::::   ::::::::          %'
echo -e '\t%               :+:    :+: :+:    :+: :+:    :+: :+:    :+:          %'
echo -e '\t%              +:+    +:+ +:+    +:+ +:+    +:+ +:+                  %'
echo -e '\t%             +#++:++#+  +#+    +:+ +#++:++#+  +#+                   %'
echo -e '\t%            +#+    +#+ +#+    +#+ +#+        +#+                    %'
echo -e '\t%           #+#    #+# #+#    #+# #+#        #+#    #+#              %'
echo -e '\t%          #########   ########  ###         ########                %'
echo -e '\t%                                                                    %'
echo -e '\t%                Block Oriented Programming Compiler                 %'
echo -e '\t%                                                                    %'
echo -e '\t%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'
echo 
msg "BOPC Installation Guide has been started ..."


# base check (we need root)
if [ "$EUID" -ne 0 ]; then
    error "Script needs root permissions to install the required packages."
    msg "Please run as 'sudo $0' (you can have a look at the source, if you don't trust me)"
    echo

    exit
fi

# install prerequisites first
apt-get install --yes python-pip
apt-get install --yes graphviz libgraphviz-dev
apt-get install --yes pkg-config python-tk 


# install pip packages
pip install angr==7.8.9.26
pip install claripy==7.8.9.26
pip install matplotlib
pip install simuvex
# networkx must be installed after simuvex and angr, since they depend
# on networkx 2.1
pip install networkx==1.11
pip install graphviz==0.8.1
pip install pygraphviz==1.3.1


msg "BOPC Installation completed ..."
msg "Have a nice day :)"
echo

# -------------------------------------------------------------------------------------------------
