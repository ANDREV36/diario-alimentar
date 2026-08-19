
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse, parse_qs
import sqlite3, json
from datetime import date

BASE=Path(__file__).resolve().parent
NUT=BASE/"banco_nutrientes.db"
DIA=BASE/"diario_alimentar.db"
HOST, PORT = "0.0.0.0", 5000
MEALS=["Café da manhã","Almoço","Lanche","Jantar","Ceia"]

NUTS=[
("energia_kcal","Calorias","kcal"),("proteina_g","Proteína","g"),
("carboidrato_g","Carboidratos","g"),("lipidios_g","Gorduras","g"),
("fibra_g","Fibras","g"),("calcio_mg","Cálcio","mg"),
("magnesio_mg","Magnésio","mg"),("manganes_mg","Manganês","mg"),
("fosforo_mg","Fósforo","mg"),("ferro_mg","Ferro","mg"),
("sodio_mg","Sódio","mg"),("potassio_mg","Potássio","mg"),
("cobre_mg","Cobre","mg"),("zinco_mg","Zinco","mg"),
("vitamina_c_mg","Vitamina C","mg"),("tiamina_mg","B1","mg"),
("riboflavina_mg","B2","mg"),("niacina_mg","B3","mg"),
("piridoxina_mg","B6","mg"),("colesterol_mg","Colesterol","mg")]

def ndb():
    c=sqlite3.connect(NUT);c.row_factory=sqlite3.Row;return c
def ddb():
    c=sqlite3.connect(DIA);c.row_factory=sqlite3.Row
    c.execute("""CREATE TABLE IF NOT EXISTS consumo(
    id INTEGER PRIMARY KEY AUTOINCREMENT,data TEXT NOT NULL,refeicao TEXT NOT NULL,
    alimento_id INTEGER,alimento_nome TEXT NOT NULL,quantidade_g REAL NOT NULL)""")
    c.commit();return c
def calc(rows):
    t={x[0]:0.0 for x in NUTS};c=ndb()
    try:
        for r in rows:
            f=c.execute("SELECT * FROM alimentos WHERE id=?",(r["alimento_id"],)).fetchone()
            if not f:continue
            z=float(r["quantidade_g"])/100
            for k,_,_ in NUTS:
                if k in f.keys() and f[k] is not None:t[k]+=float(f[k])*z
    finally:c.close()
    return t

HTML=r"""
<!doctype html><html lang="pt-BR"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>V11 - Diário Alimentar</title>
<style>
*{box-sizing:border-box}body{margin:0;background:#f2f4f7;color:#17202a;font-family:Arial}
header{background:#111827;color:white;padding:16px;position:sticky;top:0;z-index:5}
header h1{margin:0;font-size:23px}header p{margin:5px 0 0;font-size:12px;opacity:.75}
main{max-width:760px;margin:auto;padding:12px}.card{background:white;border-radius:16px;padding:14px;margin-bottom:12px;box-shadow:0 2px 8px #0001}
h2{font-size:16px;margin:0 0 12px}.date{display:flex;gap:8px}.date input{flex:1;padding:11px;border:1px solid #ddd;border-radius:10px;font-size:16px}.date button,.add button{background:#111827;color:white;border:0;border-radius:10px;padding:12px;font-weight:bold}
.meals{display:grid;grid-template-columns:1fr 1fr;gap:8px}.meals button{border:0;border-radius:12px;padding:14px 4px;background:#e5e7eb;font-weight:bold}.meals .on{background:#111827;color:white}
.search{width:100%;padding:13px;border:1px solid #ddd;border-radius:10px;font-size:16px}.foods{max-height:200px;overflow:auto}.food{padding:11px;border-bottom:1px solid #eee}
.add{display:flex;gap:8px;margin-top:10px}.add input{width:105px;padding:12px;border:1px solid #ddd;border-radius:10px;font-size:16px}.add button{flex:1}
.sel{font-size:13px;color:#667085;margin-top:8px}.item{display:flex;justify-content:space-between;gap:8px;padding:11px 0;border-bottom:1px solid #eee}.name{font-weight:bold}.info{font-size:12px;color:#667085;margin-top:3px}.act{display:flex;gap:4px}.act button{border:0;border-radius:8px;padding:7px;background:#eee}
.metrics{display:grid;grid-template-columns:1fr 1fr;gap:8px}.metric{background:#f8fafc;border-radius:12px;padding:10px}.metric small{color:#667085}.metric b{display:block;font-size:18px;margin:3px 0}.empty{text-align:center;color:#667085;padding:14px}
@media(min-width:650px){.meals{grid-template-columns:repeat(5,1fr)}}
</style></head><body>
<header><h1>V11 · Diário Alimentar</h1><p>Alimentação, nutrientes e histórico</p></header><main>
<div class="card"><h2>Data</h2><div class="date"><input id="day" type="date"><button onclick="refresh()">OK</button></div></div>
<div class="card"><h2>Refeição</h2><div id="meals" class="meals"></div></div>
<div class="card"><h2>Adicionar alimento</h2>
<input id="search" class="search" placeholder="Digite o nome do alimento..."><div id="foods" class="foods"></div>
<div class="add"><input id="weight" type="number" value="100" min="0.1" step="0.1"><button onclick="add()">ADICIONAR</button></div>
<div id="sel" class="sel">Nenhum alimento selecionado.</div></div>
<div class="card"><h2>Alimentos consumidos</h2><div id="items"></div></div>
<div class="card"><h2>Acumulado: <span id="pm"></span></h2><div id="partial" class="metrics"></div></div>
<div class="card"><h2>Total do dia</h2><div id="daily" class="metrics"></div></div>
</main>
<script>
const meals=["Café da manhã","Almoço","Lanche","Jantar","Ceia"];let meal=meals[0],chosen=null,timer;
day.value=new Date().toISOString().slice(0,10);
function fmt(x){return Number(x||0).toLocaleString("pt-BR",{minimumFractionDigits:2,maximumFractionDigits:2})}
function esc(s){return String(s).replace(/[&<>"']/g,m=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[m]))}
async function api(u,o){let r=await fetch(u,o),j=await r.json();if(!r.ok)throw Error(j.error||"Erro");return j}
function mealsUI(){mealsEl.innerHTML=meals.map(m=>"<button class='"+(m==meal?"on":"")+"' onclick='meal="+JSON.stringify(m)+";mealsUI();refresh()'>"+m+"</button>").join("");pm.textContent=meal}
async function search(){let q=searchEl.value.trim();if(!q){foods.innerHTML="";return}let j=await api("/api/foods?q="+encodeURIComponent(q));foods.innerHTML=j.foods.map(f=>"<div class='food' onclick='chosen="+JSON.stringify(f)+";sel.textContent=\"Selecionado: \"+chosen.nome;foods.innerHTML=\"\"'>"+esc(f.nome)+"</div>").join("")||"<div class='empty'>Nenhum alimento encontrado.</div>"}
async function add(){if(!chosen){alert("Selecione um alimento.");return}let w=Number(weight.value);if(w<=0){alert("Peso inválido.");return}await api("/api/consume",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({data:day.value,refeicao:meal,alimento_id:chosen.id,alimento_nome:chosen.nome,quantidade_g:w})});searchEl.value="";foods.innerHTML="";sel.textContent="Nenhum alimento selecionado.";chosen=null;refresh()}
async function refresh(){let j=await api("/api/day?data="+day.value+"&refeicao="+encodeURIComponent(meal));items.innerHTML=j.items.map(x=>"<div class='item'><div><div class='name'>"+esc(x.alimento_nome)+"</div><div class='info'>"+esc(x.refeicao)+" · "+fmt(x.quantidade_g)+" g · "+fmt(x.kcal)+" kcal</div></div><div class='act'><button onclick='edit("+x.id+")'>Alterar</button><button onclick='del("+x.id+")'>Excluir</button></div></div>").join("")||"<div class='empty'>Nenhum alimento neste dia.</div>";draw(partial,j.partial);draw(daily,j.daily)}
function draw(el,t){let a=[["energia_kcal","Calorias","kcal"],["proteina_g","Proteína","g"],["carboidrato_g","Carboidratos","g"],["lipidios_g","Gorduras","g"],["fibra_g","Fibras","g"],["calcio_mg","Cálcio","mg"],["magnesio_mg","Magnésio","mg"],["manganes_mg","Manganês","mg"],["fosforo_mg","Fósforo","mg"],["ferro_mg","Ferro","mg"],["sodio_mg","Sódio","mg"],["potassio_mg","Potássio","mg"],["cobre_mg","Cobre","mg"],["zinco_mg","Zinco","mg"],["vitamina_c_mg","Vitamina C","mg"],["tiamina_mg","B1","mg"],["riboflavina_mg","B2","mg"],["niacina_mg","B3","mg"],["piridoxina_mg","B6","mg"],["colesterol_mg","Colesterol","mg"]];el.innerHTML=a.map(n=>"<div class='metric'><small>"+n[1]+"</small><b>"+fmt(t[n[0]])+"</b><small>"+n[2]+"</small></div>").join("")}
async function del(id){if(confirm("Excluir este alimento?")){await api("/api/consume/"+id,{method:"DELETE"});refresh()}}
async function edit(id){let j=await api("/api/consume/"+id),x=j.item;let w=prompt("Peso em gramas:",x.quantidade_g);if(w===null)return;let r=prompt("Refeição:",x.refeicao);if(r===null)return;if(!meals.includes(r)||Number(w)<=0){alert("Dados inválidos.");return}await api("/api/consume/"+id,{method:"PUT",headers:{"Content-Type":"application/json"},body:JSON.stringify({quantidade_g:Number(w),refeicao:r})});refresh()}
const searchEl=document.getElementById("search"),foods=document.getElementById("foods"),items=document.getElementById("items"),partial=document.getElementById("partial"),daily=document.getElementById("daily"),sel=document.getElementById("sel"),mealsEl=document.getElementById("meals"),pm=document.getElementById("pm");
searchEl.oninput=()=>{clearTimeout(timer);timer=setTimeout(search,120)};mealsUI();refresh();
</script></body></html>
"""

class H(BaseHTTPRequestHandler):
    def js(self,o,s=200):
        b=json.dumps(o,ensure_ascii=False).encode();self.send_response(s);self.send_header("Content-Type","application/json; charset=utf-8");self.send_header("Content-Length",str(len(b)));self.end_headers();self.wfile.write(b)
    def body(self):
        return json.loads(self.rfile.read(int(self.headers.get("Content-Length","0"))).decode() or "{}")
    def do_GET(self):
        p=urlparse(self.path)
        if p.path=="/":
            b=HTML.encode();self.send_response(200);self.send_header("Content-Type","text/html; charset=utf-8");self.send_header("Content-Length",str(len(b)));self.end_headers();self.wfile.write(b);return
        if p.path=="/api/foods":
            q=parse_qs(p.query).get("q",[""])[0].lower();c=ndb()
            try:r=c.execute("SELECT id,nome FROM alimentos WHERE lower(nome) LIKE ? ORDER BY nome LIMIT 50",(f"%{q}%",)).fetchall() if q else []
            finally:c.close()
            self.js({"foods":[dict(x) for x in r]});return
        if p.path=="/api/day":
            q=parse_qs(p.query);d=q.get("data",[date.today().isoformat()])[0];m=q.get("refeicao",[MEALS[0]])[0];c=ddb()
            try:rows=c.execute("SELECT * FROM consumo WHERE data=? ORDER BY id",(d,)).fetchall()
            finally:c.close()
            c=ndb();items=[]
            try:
                for x in rows:
                    f=c.execute("SELECT energia_kcal FROM alimentos WHERE id=?",(x["alimento_id"],)).fetchone();z=x["quantidade_g"]/100
                    items.append({"id":x["id"],"refeicao":x["refeicao"],"alimento_nome":x["alimento_nome"],"quantidade_g":x["quantidade_g"],"kcal":(f["energia_kcal"] or 0)*z if f else 0})
            finally:c.close()
            self.js({"items":items,"daily":calc(rows),"partial":calc([x for x in rows if x["refeicao"]==m])});return
        if p.path.startswith("/api/consume/"):
            i=int(p.path.rsplit("/",1)[1]);c=ddb()
            try:r=c.execute("SELECT * FROM consumo WHERE id=?",(i,)).fetchone()
            finally:c.close()
            self.js({"item":dict(r)} if r else {"error":"Não encontrado"},200 if r else 404);return
        self.send_error(404)
    def do_POST(self):
        if self.path!="/api/consume":self.send_error(404);return
        try:
            x=self.body();w=float(x["quantidade_g"]);c=ddb();c.execute("INSERT INTO consumo(data,refeicao,alimento_id,alimento_nome,quantidade_g) VALUES(?,?,?,?,?)",(x["data"],x["refeicao"],x["alimento_id"],x["alimento_nome"],w));c.commit();c.close();self.js({"ok":True})
        except Exception as e:self.js({"error":str(e)},400)
    def do_PUT(self):
        try:
            i=int(self.path.rsplit("/",1)[1]);x=self.body();w=float(x["quantidade_g"]);c=ddb();c.execute("UPDATE consumo SET quantidade_g=?,refeicao=? WHERE id=?",(w,x["refeicao"],i));c.commit();c.close();self.js({"ok":True})
        except Exception as e:self.js({"error":str(e)},400)
    def do_DELETE(self):
        try:
            i=int(self.path.rsplit("/",1)[1]);c=ddb();c.execute("DELETE FROM consumo WHERE id=?",(i,));c.commit();c.close();self.js({"ok":True})
        except Exception as e:self.js({"error":str(e)},400)

if __name__=="__main__":
    if not NUT.exists(): print("ERRO: banco_nutrientes.db não encontrado.");input("ENTER para sair...");raise SystemExit
    print("V11 MOBILE iniciado.");print("No PC: http://127.0.0.1:5000");print("Para encerrar: Ctrl+C")
    ThreadingHTTPServer((HOST,PORT),H).serve_forever()
