-- Migração multiusuário do Diário Alimentar.
-- O app.py também executa CREATE TABLE IF NOT EXISTS para facilitar o primeiro deploy.

CREATE TABLE IF NOT EXISTS usuarios (
  id BIGSERIAL PRIMARY KEY,
  email TEXT NOT NULL UNIQUE,
  senha_hash TEXT NOT NULL,
  criado_em TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS sessoes (
  id BIGSERIAL PRIMARY KEY,
  usuario_id BIGINT NOT NULL REFERENCES usuarios(id) ON DELETE CASCADE,
  token_hash TEXT NOT NULL UNIQUE,
  criado_em TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  expira_em TIMESTAMPTZ NOT NULL
);

CREATE TABLE IF NOT EXISTS perfis (
  usuario_id BIGINT PRIMARY KEY REFERENCES usuarios(id) ON DELETE CASCADE,
  nome TEXT NOT NULL DEFAULT '', idade INTEGER, sexo TEXT, peso_kg REAL,
  altura_cm REAL, atividade TEXT, objetivo TEXT, peso_meta_kg REAL,
  ritmo_kg_semana REAL
);

CREATE TABLE IF NOT EXISTS metas_usuario (
  usuario_id BIGINT PRIMARY KEY REFERENCES usuarios(id) ON DELETE CASCADE,
  calorias_kcal REAL NOT NULL DEFAULT 2300,
  proteina_g REAL NOT NULL DEFAULT 180,
  carboidratos_g REAL NOT NULL DEFAULT 220,
  gorduras_g REAL NOT NULL DEFAULT 70,
  fibras_g REAL NOT NULL DEFAULT 30,
  sodio_mg REAL NOT NULL DEFAULT 2000,
  agua_ml REAL NOT NULL DEFAULT 4000,
  manual_override BOOLEAN NOT NULL DEFAULT FALSE,
  atualizado_em TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS favoritos (
  id BIGSERIAL PRIMARY KEY,
  usuario_id BIGINT NOT NULL REFERENCES usuarios(id) ON DELETE CASCADE,
  alimento_id INTEGER NOT NULL,
  alimento_nome TEXT NOT NULL,
  criado_em TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  UNIQUE(usuario_id, alimento_id)
);

CREATE TABLE IF NOT EXISTS porcoes (
  id BIGSERIAL PRIMARY KEY,
  usuario_id BIGINT NOT NULL REFERENCES usuarios(id) ON DELETE CASCADE,
  alimento_id INTEGER NOT NULL,
  alimento_nome TEXT NOT NULL,
  nome TEXT NOT NULL,
  quantidade_g REAL NOT NULL,
  criado_em TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  UNIQUE(usuario_id, alimento_id, nome)
);

CREATE TABLE IF NOT EXISTS alimentos_usuario (
  id BIGSERIAL PRIMARY KEY,
  usuario_id BIGINT NOT NULL REFERENCES usuarios(id) ON DELETE CASCADE,
  nome TEXT NOT NULL,
  energia_kcal REAL, proteina_g REAL, carboidrato_g REAL,
  lipidios_g REAL, fibra_g REAL, colesterol_mg REAL,
  calcio_mg REAL, magnesio_mg REAL, fosforo_mg REAL, ferro_mg REAL,
  sodio_mg REAL, potassio_mg REAL, zinco_mg REAL, vitamina_c_mg REAL,
  porcao_valor REAL, porcao_unidade TEXT, base_calculo TEXT DEFAULT '100g',
  criado_em TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  atualizado_em TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

ALTER TABLE consumo ADD COLUMN IF NOT EXISTS usuario_id BIGINT;
ALTER TABLE hidratacao ADD COLUMN IF NOT EXISTS usuario_id BIGINT;
CREATE INDEX IF NOT EXISTS idx_consumo_usuario_data ON consumo(usuario_id, data);
CREATE INDEX IF NOT EXISTS idx_hidratacao_usuario_data ON hidratacao(usuario_id, data);
CREATE INDEX IF NOT EXISTS idx_alimentos_usuario_nome ON alimentos_usuario(usuario_id, nome);
