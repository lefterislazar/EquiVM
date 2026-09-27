pragma solidity ^0.8.28;

contract ClipperVat {
    uint256 public sucked;
    uint256 public fluxed;
    function suck(address,address,uint256 rad) external { sucked += rad; }
    function flux(bytes32,address,address,uint256 wad) external { fluxed += wad; }
}
contract ClipperDog {
    uint256 public dug;
    function digs(bytes32,uint256 rad) external { dug += rad; }
}
contract ClipperStandalone {
    mapping(address=>uint256) public wards;
    mapping(uint256=>uint256) public saleTab;
    mapping(uint256=>uint256) public saleLot;
    mapping(uint256=>address) public saleUsr;
    bytes32 public ilk; uint256 public kicks; uint256 public stopped; address public vow;
    ClipperVat public vat; ClipperDog public dog;
    modifier auth(){require(wards[msg.sender]==1);_;}
    constructor(address vat_,address dog_,bytes32 ilk_){require(vat_!=dog_);wards[msg.sender]=1;vat=ClipperVat(vat_);dog=ClipperDog(dog_);ilk=ilk_;}
    function rely(address u) external auth{wards[u]=1;}
    function deny(address u) external auth{wards[u]=0;}
    function fileStopped(uint256 x) external auth{stopped=x;}
    function fileVow(address x) external auth{vow=x;}
    function kick(uint256 tab,uint256 lot,address usr,address kpr) external auth returns(uint256 id){
        require(stopped<1&&tab>0&&lot>0&&usr!=address(0)); id=++kicks;
        vat.suck(vow,kpr,1);
    }
    function redo(uint256 id,address kpr) external{require(stopped<2&&saleUsr[id]!=address(0));vat.suck(vow,kpr,1);}
    function yank(uint256 id) external auth{require(saleUsr[id]!=address(0));dog.digs(ilk,saleTab[id]);vat.flux(ilk,address(this),msg.sender,saleLot[id]);}
}
