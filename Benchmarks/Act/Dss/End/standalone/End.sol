pragma solidity ^0.8.28;

contract EndVat { uint256 public cages; function cage() external { cages += 1; } }
contract EndCat { uint256 public cages; function cage() external { cages += 1; } }
contract EndDog { uint256 public cages; function cage() external { cages += 1; } }

contract EndStandalone {
    mapping(address=>uint256) public wards; uint256 public live; uint256 public wait;
    EndVat public vat; EndCat public cat; EndDog public dog;
    modifier auth(){require(wards[msg.sender]==1);_;}
    constructor(address vat_,address cat_,address dog_){
        require(vat_!=cat_&&vat_!=dog_&&cat_!=dog_);wards[msg.sender]=1;live=1;
        vat=EndVat(vat_);cat=EndCat(cat_);dog=EndDog(dog_);
    }
    function rely(address u) external auth{wards[u]=1;}
    function deny(address u) external auth{wards[u]=0;}
    function fileWait(uint256 x) external auth{require(live==1);wait=x;}
    function cage() external auth{require(live==1);live=0;vat.cage();cat.cage();dog.cage();}
}
