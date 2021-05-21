class {:autocontracts} Pilha
{
    ghost const TamanhoMaximo: int;
    ghost var Conteudo: seq<int>;
    var lista: array<int>;
    var posPilha: int;
    const max: int;

    predicate Valid()
    {
        max > 0
        && max == lista.Length
        && 0 <= posPilha <= max
        && TamanhoMaximo == max
        && Conteudo == lista[0..posPilha]
    }

    constructor (n:int)
    requires n > 0
    ensures TamanhoMaximo == n
    ensures Conteudo == []
    {
        max := n;
        lista := new int[n];
        posPilha := 0;
        TamanhoMaximo := max;
        Conteudo := [];
    }

    method Empilhar(e:int) returns (valido:bool)
    requires |Conteudo| < TamanhoMaximo
    ensures Conteudo == old(Conteudo) + [e]
    ensures valido <==> (e in Conteudo)
    {
        if (posPilha <= lista.Length){ //valida espaço na pilha
            lista[posPilha] := e;
            posPilha := posPilha + 1;
            Conteudo := Conteudo + [e];
            return true;
        }
        return false;
    } 

    method Desempilhar()
    requires |Conteudo| < TamanhoMaximo
    ensures Conteudo == lista[0..posPilha]
    {
        if (posPilha > 0){ //testa pilha vazia
            posPilha := posPilha - 1;
            lista[posPilha] :=  0;
            Conteudo := lista[0..posPilha];
        }
         print "\nNenhum elemento na pilha para ser desempilhado"; 
    }

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

    method Quantidade() returns (n:int)
    ensures n == |Conteudo|
    ensures Conteudo == old(Conteudo)
    {
        n := posPilha;
    }

    method QuantidadeMaxima() returns (n:int)
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
    assert vazia == true; 
    var cheia := pilha.Cheia();
    assert cheia == false; 

    var empilhou := pilha.Empilhar(1);
    assert empilhou == true;
    pilha.Desempilhar();
}