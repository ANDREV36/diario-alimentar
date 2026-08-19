# Diario Alimentar

Aplicacao web responsiva para registrar alimentos, refeicoes e hidratacao, consultar nutrientes e acompanhar metas nutricionais.

## Recursos

- Busca de alimentos na base nutricional SQLite.
- Registro por data e refeicao.
- Calculo de calorias e nutrientes do periodo e do dia.
- Controle de hidratacao.
- Perfil, metas e resumo nutricional.
- Interface acessivel pelo navegador em computador ou celular.

## Requisitos

- Python 3.10 ou superior.
- PostgreSQL para os dados do diario.
- `banco_nutrientes.db` na raiz do projeto.

## Instalacao

```powershell
python -m venv .venv
.\.venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
```

Defina a conexao do PostgreSQL antes de iniciar:

```powershell
$env:DATABASE_URL = "postgresql://usuario:senha@localhost:5432/diario_alimentar"
python app.py
```

Abra `http://127.0.0.1:5000` no navegador. A porta pode ser alterada com a variavel `PORT`.

## Deploy

Para plataformas como Render, configure:

- Build command: `pip install -r requirements.txt`
- Start command: `python app.py`
- Variavel de ambiente: `DATABASE_URL` com a URL do PostgreSQL

O arquivo `diario_alimentar.db` e caches locais nao sao versionados. O banco de nutrientes (`banco_nutrientes.db`) e mantido no repositorio porque e utilizado pela busca de alimentos.

## Estrutura principal

- `app.py`: versao principal da aplicacao.
- `appbk.py` e `appbk2.py`: versoes de backup.
- `banco_nutrientes.db`: base local de alimentos e nutrientes.
- `a_wide_high_resolution_panoramic_landscape_photo.png`: imagem usada pela interface.
