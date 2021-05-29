//GRUPO: Eduardo Lima Dornelles e João Lucas de Almeida
class {:autocontracts} Pilha
{
    //abstração
    ghost const TamanhoMaximo: int;
    ghost var Conteudo: seq<int>;
    //implementação
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
    ensures valido <==> (Conteudo == old(Conteudo) + [e]) && posPilha > old(posPilha) && old(posPilha) < max && lista[old(posPilha)] == e
    ensures !valido <==> Conteudo == old(Conteudo) && posPilha == old(posPilha) && posPilha == max
    {
        if (posPilha < max){ //valida espaço na pilha
            lista[posPilha] := e;
            posPilha := posPilha + 1;
            Conteudo := Conteudo + [e];
            return true;
        } 
         return false;
    } 

    method Desempilhar()
    ensures if old(posPilha) > 0 then  posPilha == old(posPilha) - 1 && lista[posPilha] ==  0  && Conteudo == lista[0..posPilha] && |Conteudo| == posPilha
    else |Conteudo| == posPilha && Conteudo == old(Conteudo) && posPilha == old(posPilha)
    {      
        if (posPilha > 0) {
              posPilha := posPilha - 1;            
              lista[posPilha] :=  0;
              Conteudo := lista[0..posPilha];
        }
    }

    method Ler()//precisa retornar ou somente printar?.
    ensures Conteudo == old(Conteudo)
    ensures posPilha == old(posPilha)
    {
        if (posPilha > 0) {
          print lista[posPilha - 1];
        } else {
          print "\nNenhum elemento na pilha para ser lido\n"; 
        }
    }

    method Cheia() returns (valido:bool)
    ensures valido <==> Conteudo == old(Conteudo) && posPilha == old(posPilha) && posPilha == max  && valido == true    
    ensures !valido <==> Conteudo == old(Conteudo) && posPilha == old(posPilha) &&  posPilha < max  && valido == false    
    ensures Valid()
    {
        if (posPilha == max){            
            return true;
        } else {
            return false;
        }
    }

    method Vazia() returns (valido:bool)
    ensures Conteudo == old(Conteudo)
    ensures valido <==> (posPilha == 0)
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

    
    method InvertePilha() returns (listaInvertida: array<int>)   
    requires |Conteudo| > 0
    ensures Conteudo == lista[0..posPilha]
    ensures posPilha == old(posPilha)
  //  ensures forall k :: 0 <= k < old(posPilha) ==> lista[k] == (lista[((posPilha)-1) - k]);
    {   
        var i := 0;
        listaInvertida := new int[max];
        while i < posPilha
        modifies listaInvertida
        invariant posPilha == old(posPilha)
        invariant 0 <= i <= posPilha + 1
        decreases posPilha - i
        {  
            i := i + 1;
            listaInvertida[i - 1] := lista[posPilha - i];           
        }
        
        lista := listaInvertida;
        Conteudo := lista[0..posPilha];
    }     
}

method Main()
{
    var pilha := new Pilha(3);
    assert pilha.TamanhoMaximo == 3;
    assert pilha.Conteudo == [];
    var q := pilha.Quantidade();
    assert q == 0;
    var vazia := pilha.Vazia();
    pilha.Ler(); //tenta ler nao tendo elementos
    assert vazia == true; 
    var cheia := pilha.Cheia();
    assert cheia == false; 

    //adiciona valores na pilha...
    var empilhou := pilha.Empilhar(1);
    assert empilhou == true;

    empilhou := pilha.Empilhar(2);
    assert empilhou == true;

    empilhou := pilha.Empilhar(3);
    assert empilhou == true;

    assert pilha.Conteudo == [1,2,3];

    //tentando colocar sem espaço na pilha
    empilhou := pilha.Empilhar(4);
    assert empilhou == false;

    //lotou a pilha
    cheia := pilha.Cheia();
    assert cheia == true; 

    //desempilha dois elementos
    pilha.Desempilhar();
    pilha.Desempilhar();

    var s := pilha.lista[..];
    //valida conteudo com o q tem na pilha..
    assert pilha.posPilha == 1; //pos 1 = tem 1 elemento na pilha
    assert pilha.Conteudo == s[0..pilha.posPilha]; // [1] == [1]
    assert pilha.Conteudo[0] == s[0];

    empilhou := pilha.Empilhar(2);
    assert empilhou == true;

    empilhou := pilha.Empilhar(3);
    assert empilhou == true;

    s := pilha.lista[..];
    print(s);
    assert pilha.posPilha == 3; //3 elementos na pilha novamente
    assert pilha.Conteudo == s[0..pilha.posPilha];
    //compara se o conteudo esta igual a lista..
    assert pilha.Conteudo[0] == s[0];
    assert pilha.Conteudo[1] == s[1];
    assert pilha.Conteudo[2] == s[2];
  //  assert pilha.Conteudo == [1,2,3];
     
    var listaInvertida := pilha.InvertePilha();

    s := pilha.lista[..];
    assert pilha.posPilha == 3; //3 elementos na pilha novamente - invertidos
    assert pilha.Conteudo == s[0..pilha.posPilha];
    //compara se o conteudo esta igual a lista..
    assert pilha.Conteudo[0] == s[0];
    assert pilha.Conteudo[1] == s[1];
    assert pilha.Conteudo[2] == s[2];
  //  assert pilha.Conteudo == [3,2,1];
    print(s);
}