pragma solidity ^0.8.28;
contract FlapperVat { uint256 public moved; function move(address,address,uint256 rad) external{moved+=rad;} }
contract FlapperStandalone {
 mapping(address=>uint256) public wards; uint256 public live; uint256 public lid; uint256 public fill; uint256 public kicks; FlapperVat public vat;
 modifier auth(){require(wards[msg.sender]==1);_;}
 constructor(address vat_){wards[msg.sender]=1;live=1;vat=FlapperVat(vat_);}
 function rely(address u) external auth{wards[u]=1;} function deny(address u) external auth{wards[u]=0;} function fileLid(uint256 x) external auth{lid=x;}
 function kick(uint256 lot,uint256) external auth returns(uint256 id){require(live==1);fill+=lot;require(fill<=lid);id=++kicks;vat.move(msg.sender,address(this),lot);}
 function cage(uint256 rad) external auth{live=0;vat.move(address(this),msg.sender,rad);}
}
