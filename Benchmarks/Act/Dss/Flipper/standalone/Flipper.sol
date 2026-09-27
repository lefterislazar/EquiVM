pragma solidity ^0.8.28;
contract FlipperVat {
 uint256 public fluxed; uint256 public moved;
 function flux(bytes32,address,address,uint256 wad) external{fluxed+=wad;}
 function move(address,address,uint256 rad) external{moved+=rad;}
}
contract FlipperCat { uint256 public clawed; function claw(uint256 rad) external{clawed+=rad;} }
contract FlipperStandalone {
 mapping(address=>uint256) public wards; mapping(uint256=>uint256) public bid; mapping(uint256=>uint256) public lot; mapping(uint256=>uint256) public tab; mapping(uint256=>address) public guy;
 uint256 public kicks; bytes32 public ilk; FlipperVat public vat; FlipperCat public cat;
 modifier auth(){require(wards[msg.sender]==1);_;}
 constructor(address vat_,address cat_,bytes32 ilk_){require(vat_!=cat_);wards[msg.sender]=1;vat=FlipperVat(vat_);cat=FlipperCat(cat_);ilk=ilk_;}
 function rely(address u) external auth{wards[u]=1;} function deny(address u) external auth{wards[u]=0;}
 function kick(address,address,uint256,uint256 lot_,uint256) external auth returns(uint256 id){id=++kicks;vat.flux(ilk,msg.sender,address(this),lot_);}
 function yank(uint256 id) external auth{require(guy[id]!=address(0)&&bid[id]<tab[id]);cat.claw(tab[id]);vat.flux(ilk,address(this),msg.sender,lot[id]);vat.move(msg.sender,guy[id],bid[id]);}
}
