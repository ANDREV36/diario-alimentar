# Diário Alimentar

Aplicação web responsiva para registrar alimentos, refeições e hidratação, acompanhar metas nutricionais e consultar o histórico diário. Esta versão suporta **várias contas independentes**, com cadastro por e-mail e senha, dados isolados por usuário, metas automáticas ou manuais, favoritos, porções salvas, exportação CSV e cadastro de alimentos personalizados.

## Funcionalidades

Cada pessoa cria sua própria conta e acessa somente seu perfil, suas metas, alimentos consumidos, hidratação, favoritos, porções e histórico. As senhas são armazenadas como hash protegido no PostgreSQL e as sessões usam cookie HTTP-only com expiração.

O perfil calcula metas iniciais a partir de idade, sexo, peso, altura, atividade e objetivo. O usuário pode editar as metas manualmente; nesse modo, salvar novamente o perfil não sobrescreve os valores. O cálculo automático pode ser reaplicado explicitamente pela tela de resumo.

A busca reúne a base nutricional interna compartilhada e os alimentos personalizados do usuário. Ao cadastrar um alimento que não esteja na base, é possível preencher os nutrientes manualmente ou fotografar a tabela nutricional. A fotografia é enviada somente ao servidor, a leitura retorna os campos para conferência e o cadastro só é salvo depois da confirmação do usuário.

O diário oferece registro por data e refeição, hidratação, favoritos, porções habituais e exportação do dia em CSV. A rota `/health` retorna `ok` e pode ser usada pelo Render para verificar se o serviço está respondendo.

## Desenvolvimento local

É necessário usar Python 3.10 ou superior e um PostgreSQL acessível. Instale as dependências com:

```bash
python -m venv .venv
# Linux/macOS
source .venv/bin/activate
# Windows PowerShell
# .\\.venv\\Scripts\\Activate.ps1
pip install -r requirements.txt
```

Defina as variáveis antes de iniciar:

```bash
export DATABASE_URL="postgresql://usuario:senha@localhost:5432/diario_alimentar"
export SESSION_SECRET="uma-chave-longa-e-aleatoria"
export OPENAI_API_KEY="sua-chave-do-servico-de-visao"
python app.py
```

A aplicação usa `PORT` quando fornecida; localmente, o padrão é `5000`.

## Deploy no Render

Crie um Web Service conectado ao repositório GitHub e configure:

| Campo | Valor |
|---|---|
| Build Command | `pip install -r requirements.txt` |
| Start Command | `python app.py` |
| Banco | PostgreSQL do Render ligado pela variável `DATABASE_URL` |

Configure no Render as variáveis abaixo. Os valores secretos devem ser inseridos diretamente no painel do Render, nunca no código ou no GitHub.

| Variável | Obrigatória | Finalidade |
|---|---:|---|
| `DATABASE_URL` | Sim | Conexão com o PostgreSQL do Render. |
| `SESSION_SECRET` | Sim | Chave usada para a segurança das sessões. |
| `OPENAI_API_KEY` | Somente para fotografias | Permite ler a tabela nutricional no servidor. |
| `VISION_MODEL` | Não | Modelo de visão; padrão configurado no código. |
| `PORT` | Não | O Render fornece automaticamente. |

Depois do primeiro deploy, acesse `/health` para verificar a disponibilidade do serviço. As tabelas novas são criadas automaticamente na primeira conexão, mas recomenda-se fazer um backup do PostgreSQL antes de atualizar uma instalação que já contenha dados antigos.

## Segurança e dados

A chave `OPENAI_API_KEY` é usada apenas no backend. A imagem da tabela é processada temporariamente e não é gravada permanentemente pelo aplicativo. Para dados de produção, mantenha backups do PostgreSQL e nunca publique `.env`, senhas ou tokens.

A base `banco_nutrientes.db` permanece no repositório como fonte nutricional compartilhada. Alimentos personalizados ficam no PostgreSQL, associados ao usuário que os criou. Registros legados da versão single-user são associados à primeira conta criada durante a migração; verifique essa conta depois do primeiro login.

As metas são estimativas para acompanhamento e não substituem avaliação individual de médico ou nutricionista.
