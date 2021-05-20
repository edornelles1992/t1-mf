class {:autocontracts} Pilha
{
    ghost const TamanhoMaximo: nat;
    ghost var Conteudo: seq<nat>;
    var lista: array<nat>;
    var posPilha: nat;
    const max: nat;

    predicate Valid()
    {
        max > 0
        && max == lista.Length
        && 0 <= posPilha <= max
        && TamanhoMaximo == max
        && Conteudo == lista[0..posPilha]
    }

    constructor (n:nat)
    requires n > 0
    ensures TamanhoMaximo == n
    ensures Conteudo == []
    {
        max := n;
        lista := new nat[n];
        posPilha := 0;
        TamanhoMaximo := max;
        Conteudo := [];
    }

    method Empilhar(e:nat) returns (valido:bool)
    requires |Conteudo| < TamanhoMaximo
    ensures Conteudo == old(Conteudo) + [e]
    {
        if (posPilha <= lista.Length){
            lista[posPilha] := e;
            posPilha := posPilha + 1;
            Conteudo := Conteudo + [e];
            return true;
        }
        return false;
    } 

   // method Desempilhar()

    method Ler()//precisa retornar ou somente printar?.
    ensures Conteudo == old(Conteudo)
    ensures posPilha == old(posPilha)
    {
        if (posPilha > 0) {
          print lista[posPilha - 1];
        } else {
          print "\nNenhum elemento na pilha para ser lido"; 
        }
    }

    method Cheia() returns (valido:bool)
    ensures Conteudo == old(Conteudo)
    ensures valido <==> (posPilha == max) //esta cheia se e somente se posPilha == max
    {
        if (posPilha == max){
            return true;
        } else {
            return false;
        }
    }

    method Vazia() returns (valido:bool)
    ensures Conteudo == old(Conteudo)
    ensures valido <==> (posPilha == 0)  // esta vazio se e somente se posPilha == 0
    {
        if (posPilha == 0){
            return true;
        } else {
            return false;
        }
    }

    method Quantidade() returns (n:nat)
    ensures n == |Conteudo|
    ensures Conteudo == old(Conteudo)
    {
        n := posPilha;
    }

    method QuantidadeMaxima() returns (n:nat)
    ensures n == TamanhoMaximo
    ensures Conteudo == old(Conteudo)
    {
        return max;
    }

//    method InvertePilha() 
}

method Main()
{
    var pilha := new Pilha(5);
    assert pilha.TamanhoMaximo == 5;
    assert pilha.Conteudo == [];
    var q := pilha.Quantidade();
    assert q == 0;
    var vazia := pilha.Vazia();
    pilha.Ler();
  //  assert vazia == true; //VER SE TA CERTO expressao ==>
  //  var cheia := pilha.Cheia();
  //  assert cheia == true; //VER SE TA CERTO expressao ==>
    assert vazia == true; 
    var cheia := pilha.Cheia();
    assert cheia == false; 
}