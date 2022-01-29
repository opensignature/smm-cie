/*
 * smm-cie.c: Secure Messaging 'Italian EID (CIE)' module
 *
 * Copyright (C) 2022  Antonio Iacono <antonio@piumarossa.it>
 * Copyright (C) 2010  Viktor Tarasov <vtarasov@opentrust.com>
 *                      OpenTrust <www.opentrust.com>
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif
#include <stdio.h>
#include <stdlib.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif

#include <string.h>
#include <assert.h>
#include <errno.h>
#include <ctype.h>
#include <sys/stat.h>

#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/err.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/des.h>
#include <openssl/dsa.h>
#include <openssl/bn.h>
#include <openssl/pkcs12.h>
#include <openssl/x509v3.h>
#include <openssl/rand.h>

#include "libopensc/opensc.h"
#include "libopensc/cards.h"
#include "libopensc/log.h"
#include "libopensc/iasecc.h"

#include "sm-module.h"

static int
sm_get_mac(struct sc_context *ctx, unsigned char *key, DES_cblock *icv,
			unsigned char *in, int in_len, DES_cblock *out, int force_padding)
{
	unsigned char padding[8] = {0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
	unsigned char *buf;

	LOG_FUNC_CALLED(ctx);
	sc_debug(ctx, SC_LOG_DEBUG_SM, "sm_get_mac() data length %i", in_len);

	buf = malloc(in_len + 8);
	if (!buf)
		LOG_FUNC_RETURN(ctx, SC_ERROR_OUT_OF_MEMORY);

	sc_debug(ctx, SC_LOG_DEBUG_SM, "sm_get_mac() in_data(%i) %s", in_len, sc_dump_hex(in, in_len));
	memcpy(buf, in, in_len);
	memcpy(buf + in_len, padding, 8);

	if (force_padding)
		in_len = ((in_len + 8) / 8) * 8;
	else
		in_len = ((in_len + 7) / 8) * 8;

	sc_debug(ctx, SC_LOG_DEBUG_SM, "sm_get_mac() data to MAC(%i) %s", in_len, sc_dump_hex(buf, in_len));
	sc_debug(ctx, SC_LOG_DEBUG_SM, "sm_get_mac() ICV %s", sc_dump_hex((unsigned char *)icv, 8));

	DES_cbc_cksum_3des_emv96(buf, out, in_len, key, icv);

	free(buf);
	LOG_FUNC_RETURN(ctx, SC_SUCCESS);
}

static int
sm_securize_apdu(struct sc_context *ctx, struct sm_info *sm_info, struct sc_remote_apdu *rapdu)
{
	struct sm_cwa_session *session_data = &sm_info->session.cwa;
	struct sc_apdu *apdu = &rapdu->apdu;
	unsigned char sbuf[0x400];
	DES_cblock cblock, icv;
	unsigned char *encrypted = NULL, edfb_data[0x200], mac_data[0x200];
	size_t encrypted_len, edfb_len = 0, mac_len = 0, offs;
	int rv;
	LOG_FUNC_CALLED(ctx);

	apdu->ins = 0x22;
	apdu->p1 = 0x81;
	apdu->p2 = 0xB6;

	sc_debug(ctx, SC_LOG_DEBUG_SM,
	       "securize APDU (cla:%X,ins:%X,p1:%X,p2:%X,data(%"SC_FORMAT_LEN_SIZE_T"u):%p)",
	       apdu->cla, apdu->ins, apdu->p1, apdu->p2, apdu->datalen,
	       apdu->data);

	sm_incr_ssc(session_data->ssc, sizeof(session_data->ssc));

	rv = sm_encrypt_des_cbc3(ctx, session_data->session_enc, apdu->data, apdu->datalen, &encrypted, &encrypted_len, 0);
	LOG_TEST_RET(ctx, rv, "securize APDU: DES CBC3 encryption failed");
	sc_debug(ctx, SC_LOG_DEBUG_SM, "encrypted data (len:%"SC_FORMAT_LEN_SIZE_T"u, %s)",
	       encrypted_len, sc_dump_hex(encrypted, encrypted_len));

	offs = 0;
	if (apdu->ins & 0x01)   {
		edfb_data[offs++] = IASECC_SM_DO_TAG_TCG_ODD_INS;
		if (encrypted_len + 1 > 0x7F)
			edfb_data[offs++] = 0x81;
		edfb_data[offs++] = encrypted_len;
	}
	else   {
		edfb_data[offs++] = IASECC_SM_DO_TAG_TCG_EVEN_INS;
		if (encrypted_len + 1 > 0x7F)
			edfb_data[offs++] = 0x81;
		edfb_data[offs++] = encrypted_len + 1;
		edfb_data[offs++] = 0x01;
	}
	memcpy(edfb_data + offs, encrypted, encrypted_len);
	offs += encrypted_len;
	edfb_len = offs;
	sc_debug(ctx, SC_LOG_DEBUG_SM, "securize APDU: EDFB(len:%"SC_FORMAT_LEN_SIZE_T"u,%s)",
	       edfb_len, sc_dump_hex(edfb_data, edfb_len));

	free(encrypted);
	encrypted = NULL;

	offs = 0;
	memcpy(mac_data + offs, session_data->ssc, 8);
	offs += 8;
	mac_data[offs++] = apdu->cla | 0x0C;
	mac_data[offs++] = apdu->ins;
	mac_data[offs++] = apdu->p1;
	mac_data[offs++] = apdu->p2;
	mac_data[offs++] = 0x80;
	mac_data[offs++] = 0x00;
	mac_data[offs++] = 0x00;
	mac_data[offs++] = 0x00;

	memcpy(mac_data + offs, edfb_data, edfb_len);
	offs += edfb_len;

	/* if (apdu->le)   { */
		mac_data[offs++] = IASECC_SM_DO_TAG_TLE;
		mac_data[offs++] = 1;
//		mac_data[offs++] = apdu->le;
		mac_data[offs++] = 0;
	/* } */

	mac_len = offs;
	sc_debug(ctx, SC_LOG_DEBUG_SM, "securize APDU: MAC data(len:%"SC_FORMAT_LEN_SIZE_T"u,%s)",
	       mac_len, sc_dump_hex(mac_data, mac_len));

	memset(icv, 0, sizeof(icv));
	rv = sm_get_mac(ctx, session_data->session_mac, &icv, mac_data, mac_len, &cblock, 0);
	LOG_TEST_RET(ctx, rv, "securize APDU: MAC calculation error");
	sc_debug(ctx, SC_LOG_DEBUG_SM, "securize APDU: MAC:%s", sc_dump_hex(cblock, sizeof(cblock)));

	offs = 0;
	if (edfb_len)   {
		memcpy(sbuf + offs, edfb_data, edfb_len);
		offs += edfb_len;
	}

	/* if (apdu->le)   { */
		sbuf[offs++] = IASECC_SM_DO_TAG_TLE;
		sbuf[offs++] = 1;
// cambiato
//		sbuf[offs++] = apdu->le;
		sbuf[offs++] = 0;
	/* } */
	sbuf[offs++] = IASECC_SM_DO_TAG_TCC;
	sbuf[offs++] = 8;
	memcpy(sbuf + offs, cblock, 8);
	offs += 8;
	sc_debug(ctx, SC_LOG_DEBUG_SM, "securize APDU: SM data(len:%"SC_FORMAT_LEN_SIZE_T"u,%s)",
	       offs, sc_dump_hex(sbuf, offs));

	if (offs > sizeof(rapdu->sbuf))
		LOG_TEST_RET(ctx, SC_ERROR_BUFFER_TOO_SMALL, "securize APDU: buffer too small for encrypted data");

	apdu->cse = SC_APDU_CASE_4_SHORT;
	apdu->cla |= 0x0C;
	apdu->lc = offs;
	apdu->datalen = offs;
	memcpy((unsigned char *)apdu->data, sbuf, offs);

	sm_incr_ssc(session_data->ssc, sizeof(session_data->ssc));

	LOG_FUNC_RETURN(ctx, SC_SUCCESS);
}

static int
sm_dh_decode_authentication_data(struct sc_context *ctx,
  struct sm_dh_session *session_data, unsigned char *auth_data)
{
	// DES_cblock icv = {0, 0, 0, 0, 0, 0, 0, 0};
	// DES_cblock cblock;
	unsigned char *decrypted = NULL;
	// size_t decrypted_len;
	// int rv;

	LOG_FUNC_CALLED(ctx);

	// memset(icv, 0, sizeof(icv));
	// rv = sm_dh_rsa_get_mac(ctx, keyset->mac, &icv, session_data->mdata, 0x40, &cblock, 1);
	// LOG_TEST_RET(ctx, rv, "Decode authentication data:  sm_ecc_get_mac failed");
	// sc_debug(ctx, SC_LOG_DEBUG_SM, "MAC:%s", sc_dump_hex(cblock, sizeof(cblock)));

	// if(memcmp(session_data->mdata + 0x40, cblock, 8))
	// 	LOG_FUNC_RETURN(ctx, SC_ERROR_SM_AUTHENTICATION_FAILED);

	// rv = sm_decrypt_des_cbc3(ctx, keyset->enc, session_data->mdata, session_data->mdata_len, &decrypted, &decrypted_len);
	// LOG_TEST_RET(ctx, rv, "sm_ecc_decode_auth_data() DES CBC3 decrypt error");

	// sc_debug(ctx, SC_LOG_DEBUG_SM,
	//        "sm_ecc_decode_auth_data() decrypted(%"SC_FORMAT_LEN_SIZE_T"u) %s",
	//        decrypted_len, sc_dump_hex(decrypted, decrypted_len));

	// if (memcmp(decrypted, session_data->icc.rnd, 8)) {
	// 	free(decrypted);
	// 	LOG_FUNC_RETURN(ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);
	// }

	// if (memcmp(decrypted + 8, session_data->icc.sn, 8)) {
	// 	free(decrypted);
	// 	LOG_FUNC_RETURN(ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);
	// }

	// if (memcmp(decrypted + 16, session_data->ifd.rnd, 8)) {
	// 	free(decrypted);
	// 	LOG_FUNC_RETURN(ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);
	// }

	// if (memcmp(decrypted + 24, session_data->ifd.sn, 8)) {
	// 	free(decrypted);
	// 	LOG_FUNC_RETURN(ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);
	// }

	// memcpy(session_data->icc.k, decrypted + 32, 32);

	free(decrypted);
	LOG_FUNC_RETURN(ctx, SC_SUCCESS);
}

static int
sm_iasecc_get_apdu_verify_pin(struct sc_context *ctx, struct sm_info *sm_info, struct sc_remote_data *rdata)
{
	struct sc_pin_cmd_data *pin_data = (struct sc_pin_cmd_data *)sm_info->cmd_data;
	struct sc_remote_apdu *rapdu = NULL;
	int rv;

	LOG_FUNC_CALLED(ctx);
	if (!pin_data || !rdata || !rdata->alloc)
		LOG_FUNC_RETURN(ctx, SC_ERROR_INVALID_ARGUMENTS);

	sc_debug(ctx, SC_LOG_DEBUG_SM, "SM get 'VERIFY PIN' APDU: %u", pin_data->pin_reference);

	rv = rdata->alloc(rdata, &rapdu);
	LOG_TEST_RET(ctx, rv, "SM get 'VERIFY PIN' APDUs: cannot allocate remote APDU");

	rapdu->apdu.cse = SC_APDU_CASE_3_SHORT;
	rapdu->apdu.cla = 0x00;
	rapdu->apdu.ins = 0x20;
	rapdu->apdu.p1 = 0x00;
	rapdu->apdu.p2 = pin_data->pin_reference & ~IASECC_OBJECT_REF_GLOBAL;
	if (pin_data->pin1.len > SM_MAX_DATA_SIZE)
		LOG_TEST_RET(ctx, rv, "SM get 'VERIFY PIN' APDU: invalid PIN size");

	memcpy((unsigned char *)rapdu->apdu.data, pin_data->pin1.data, pin_data->pin1.len);
	rapdu->apdu.datalen = pin_data->pin1.len;
	rapdu->apdu.lc = pin_data->pin1.len;

	/** 99 02 SW   8E 08 MAC **/
	rapdu->apdu.le = 0x0E;

	rv = sm_securize_apdu(ctx, sm_info, rapdu);
	LOG_TEST_RET(ctx, rv, "SM get 'VERIFY PIN' APDUs: securize APDU error");

	rapdu->flags |= SC_REMOTE_APDU_FLAG_RETURN_ANSWER;

	LOG_FUNC_RETURN(ctx, rv);
}

static int
sm_iasecc_get_apdu_generate_rsa(struct sc_context *ctx, struct sm_info *sm_info, struct sc_remote_data *rdata)
{
	struct iasecc_sdo *sdo = (struct iasecc_sdo *)sm_info->cmd_data;
	struct sc_remote_apdu *rapdu = NULL;
	unsigned char put_exponent_data[14] = {
		0x70, 0x0C,
			IASECC_SDO_TAG_HEADER, IASECC_SDO_CLASS_RSA_PUBLIC | 0x80, sdo->sdo_ref & 0x7F, 0x08,
					0x7F, 0x49, 0x05, 0x82, 0x03, 0x01, 0x00, 0x01
	};
	unsigned char generate_data[5] = {
		0x70, 0x03,
			IASECC_SDO_TAG_HEADER, IASECC_SDO_CLASS_RSA_PRIVATE | 0x80, sdo->sdo_ref & 0x7F
	};
	int rv;

	LOG_FUNC_CALLED(ctx);
	sc_debug(ctx, SC_LOG_DEBUG_SM, "SM get 'GENERATE RSA' APDU: SDO(class:%X,reference:%X)", sdo->sdo_class, sdo->sdo_ref);

        if (!rdata || !rdata->alloc)
		LOG_FUNC_RETURN(ctx, SC_ERROR_INVALID_ARGUMENTS);

	/* Put Exponent */
 	rv = rdata->alloc(rdata, &rapdu);
	LOG_TEST_RET(ctx, rv, "SM get 'UPDATE BINARY' APDUs: cannot allocate remote APDU");

	rapdu->apdu.cse = SC_APDU_CASE_3_SHORT;
	rapdu->apdu.cla = 0x00;
	rapdu->apdu.ins = 0xDB;
	rapdu->apdu.p1 = 0x3F;
	rapdu->apdu.p2 = 0xFF;
	memcpy((unsigned char *)rapdu->apdu.data, put_exponent_data, sizeof(put_exponent_data));
	rapdu->apdu.datalen = sizeof(put_exponent_data);
	rapdu->apdu.lc = sizeof(put_exponent_data);

	/** 99 02 SW   8E 08 MAC **/
	rapdu->apdu.le = 0x0E;

	rv = sm_securize_apdu(ctx, sm_info, rapdu);
	LOG_TEST_RET(ctx, rv, "SM get 'UPDATE BINARY' APDUs: securize APDU error");

	rapdu->flags |= SC_REMOTE_APDU_FLAG_RETURN_ANSWER;

	/* Generate Key */
 	rv = rdata->alloc(rdata, &rapdu);
	LOG_TEST_RET(ctx, rv, "SM get 'UPDATE BINARY' APDUs: cannot allocate remote APDU");

	rapdu->apdu.cse = SC_APDU_CASE_4_SHORT;
	rapdu->apdu.cla = 0x00;
	rapdu->apdu.ins = 0x47;
	rapdu->apdu.p1 = 0x00;
	rapdu->apdu.p2 = 0x00;
	memcpy((unsigned char *)rapdu->apdu.data, generate_data, sizeof(generate_data));
	rapdu->apdu.datalen = sizeof(generate_data);
	rapdu->apdu.lc = sizeof(generate_data);

	rapdu->apdu.le = 0x100;

	rv = sm_securize_apdu(ctx, sm_info, rapdu);
	LOG_TEST_RET(ctx, rv, "SM get 'UPDATE BINARY' APDUs: securize APDU error");

	rapdu->flags |= SC_REMOTE_APDU_FLAG_RETURN_ANSWER;

	LOG_FUNC_RETURN(ctx, rv);
}


static int
sm_iasecc_get_apdu_update_rsa(struct sc_context *ctx, struct sm_info *sm_info, struct sc_remote_data *rdata)
{
	struct iasecc_sdo_rsa_update *cmd_data = (struct iasecc_sdo_rsa_update *)sm_info->cmd_data;
	struct iasecc_sdo_update *to_update[2] = {NULL, NULL};
	int rv = 0, ii = 0, jj = 0;

	LOG_FUNC_CALLED(ctx);
	if (cmd_data->update_prv.sdo_class)   {
		to_update[ii++] = &cmd_data->update_prv;
		sc_debug(ctx, SC_LOG_DEBUG_SM, "SM get 'UPDATE RSA' APDU: SDO(class:%X,ref:%X)", cmd_data->update_prv.sdo_class, cmd_data->update_prv.sdo_ref);
	}

	if (cmd_data->update_pub.sdo_class)   {
		to_update[ii++] = &cmd_data->update_pub;
		sc_debug(ctx, SC_LOG_DEBUG_SM, "SM get 'UPDATE RSA' APDU: SDO(class:%X,ref:%X)", cmd_data->update_pub.sdo_class, cmd_data->update_pub.sdo_ref);
	}

	for (jj = 0; jj < 2 && to_update[jj]; jj++)   {
		for (ii = 0; ii < IASECC_SDO_TAGS_UPDATE_MAX && to_update[jj]->fields[ii].tag; ii++)   {
			unsigned char *encoded = NULL;
			size_t encoded_len, offs;

			sc_debug(ctx, SC_LOG_DEBUG_SM, "SM IAS/ECC get APDUs: component(num %i:%i) class:%X, ref:%X", jj, ii,
					to_update[jj]->sdo_class, to_update[jj]->sdo_ref);

			encoded_len = iasecc_sdo_encode_update_field(ctx, to_update[jj]->sdo_class, to_update[jj]->sdo_ref,
						&to_update[jj]->fields[ii], &encoded);
			LOG_TEST_RET(ctx, encoded_len, "SM get 'UPDATE RSA' APDU: cannot encode key component");

			sc_debug(ctx, SC_LOG_DEBUG_SM, "SM IAS/ECC get APDUs: component encoded %s", sc_dump_hex(encoded, encoded_len));

			for (offs = 0; offs < encoded_len; )   {
				int len = (encoded_len - offs) > SM_MAX_DATA_SIZE ? SM_MAX_DATA_SIZE : (encoded_len - offs);
				struct sc_remote_apdu *rapdu = NULL;

		 		rv = rdata->alloc(rdata, &rapdu);
	        		LOG_TEST_RET(ctx, rv, "SM get 'UPDATE RSA' APDUs: cannot allocate remote APDU");

				rapdu->apdu.cse = SC_APDU_CASE_3_SHORT;
				rapdu->apdu.cla = len + offs < encoded_len ? 0x10 : 0x00;
				rapdu->apdu.ins = 0xDB;
				rapdu->apdu.p1 = 0x3F;
				rapdu->apdu.p2 = 0xFF;
				memcpy((unsigned char *)rapdu->apdu.data, encoded + offs, len);
				rapdu->apdu.datalen = len;
				rapdu->apdu.lc = len;

				/** 99 02 SW   8E 08 MAC **/
				rapdu->apdu.le = 0x0E;

				rv = sm_securize_apdu(ctx, sm_info, rapdu);
		                LOG_TEST_RET(ctx, rv, "SM get 'UPDATE RSA' APDUs: securize APDU error");

				rapdu->flags |= SC_REMOTE_APDU_FLAG_RETURN_ANSWER;

				offs += len;
			}
			free(encoded);
		}
	}

	LOG_FUNC_RETURN(ctx, SC_SUCCESS);
}

static int
sm_iasecc_get_apdu_read_binary(struct sc_context *ctx, struct sm_info *sm_info, struct sc_remote_data *rdata)
{
	struct iasecc_sm_cmd_update_binary *cmd_data = (struct iasecc_sm_cmd_update_binary *)sm_info->cmd_data;
	size_t offs, data_offs = 0;
	int rv = 0;

	LOG_FUNC_CALLED(ctx);
	if (!cmd_data || !cmd_data->data)
		LOG_FUNC_RETURN(ctx, SC_ERROR_INVALID_ARGUMENTS);

        if (!rdata || !rdata->alloc)
		LOG_FUNC_RETURN(ctx, SC_ERROR_INVALID_ARGUMENTS);

	sc_debug(ctx, SC_LOG_DEBUG_SM,
	       "SM get 'READ BINARY' APDUs: offset:%"SC_FORMAT_LEN_SIZE_T"u,size:%"SC_FORMAT_LEN_SIZE_T"u",
	       cmd_data->offs, cmd_data->count);
	offs = cmd_data->offs;
	while (cmd_data->count > data_offs)   {
		int sz = (cmd_data->count - data_offs) > SM_MAX_DATA_SIZE ? SM_MAX_DATA_SIZE : (cmd_data->count - data_offs);
		struct sc_remote_apdu *rapdu = NULL;

 		rv = rdata->alloc(rdata, &rapdu);
	        LOG_TEST_RET(ctx, rv, "SM get 'READ BINARY' APDUs: cannot allocate remote APDU");

		rapdu->apdu.cse = SC_APDU_CASE_2_SHORT;
		rapdu->apdu.cla = 0x00;
		rapdu->apdu.ins = 0xB0;
		rapdu->apdu.p1 = (offs >> 8) & 0xFF;
		rapdu->apdu.p2 = offs & 0xFF;
//		rapdu->apdu.le = sz;
		rapdu->apdu.le = 0;
		/* 'resplen' cambiato is set by remote apdu allocation procedure */

		rv = sm_securize_apdu(ctx, sm_info, rapdu);
		LOG_TEST_RET(ctx, rv, "SM get 'UPDATE BINARY' APDUs: securize APDU error");

		rapdu->flags |= SC_REMOTE_APDU_FLAG_RETURN_ANSWER;

		offs += sz;
		data_offs += sz;
	}

	LOG_FUNC_RETURN(ctx, rv);
}

/** API of the external SM module */
/**
 * Initialize
 *
 * Read keyset from the OpenSC configuration file,
 * get and return the APDU(s) to initialize SM session.
 */
int
initialize(struct sc_context *ctx, struct sm_info *sm_info, struct sc_remote_data *out)
{
	int rv = SC_ERROR_NOT_SUPPORTED;

	LOG_FUNC_CALLED(ctx);
	if (!sm_info)
		LOG_FUNC_RETURN(ctx, SC_ERROR_INVALID_ARGUMENTS);

	sc_debug(ctx, SC_LOG_DEBUG_SM, "Current AID: %s", sc_dump_hex(sm_info->current_aid.value, sm_info->current_aid.len));
	switch (sm_info->sm_type)   {
		case SM_TYPE_DH_RSA:
			// rv = sm_dh_rsa_config_get_keyset(ctx, sm_info);
			// LOG_TEST_RET(ctx, rv, "SM DH RSA iasecc configuration error");

			rv = sm_dh_rsa_initialize(ctx, sm_info, out);
			LOG_TEST_RET(ctx, rv, "SM DH RSA iasecc initializing error");
			rv = sm_dh_rsa_init_session_keys(ctx, &sm_info->session.dh, IASECC_ALGORITHM_ASYMMETRIC_SHA256);
			LOG_TEST_RET(ctx, rv, "SM DH RSA iasecc initializing error");
			break;
		default:
			LOG_TEST_RET(ctx, SC_ERROR_NOT_SUPPORTED, "unsupported SM type");
	};

	LOG_FUNC_RETURN(ctx, rv);
}


/**
 * Get APDU(s)
 *
 * Get securized APDU(s) corresponding
 * to the asked command.
 */
int
get_apdus(struct sc_context *ctx, struct sm_info *sm_info, unsigned char *init_data, size_t init_len,
		struct sc_remote_data *rdata)
{
	struct sm_dh_session *dh_session = &sm_info->session.dh;
	int rv = SC_ERROR_NOT_SUPPORTED;

	LOG_FUNC_CALLED(ctx);
	if (!sm_info)
		LOG_FUNC_RETURN(ctx, SC_ERROR_INVALID_ARGUMENTS);

	sc_debug(ctx, SC_LOG_DEBUG_SM, "SM get APDUs: rdata:%p", rdata);
	sc_debug(ctx, SC_LOG_DEBUG_SM, "SM get APDUs: serial %s", sc_dump_hex(sm_info->serialnr.value, sm_info->serialnr.len));

	rv = sm_dh_decode_authentication_data(ctx, dh_session, init_data);
	LOG_TEST_RET(ctx, rv, "SM IAS/ECC get APDUs: decode authentication data error");

	// rv = sm_cwa_init_session_keys(ctx, cwa_session, cwa_session->params.crt_at.algo);
	// LOG_TEST_RET(ctx, rv, "SM IAS/ECC get APDUs: cannot get session keys");

	// sc_debug(ctx, SC_LOG_DEBUG_SM, "SKENC %s", sc_dump_hex(cwa_session->session_enc, sizeof(cwa_session->session_enc)));
	// sc_debug(ctx, SC_LOG_DEBUG_SM, "SKMAC %s", sc_dump_hex(cwa_session->session_mac, sizeof(cwa_session->session_mac)));
	// sc_debug(ctx, SC_LOG_DEBUG_SM, "SSC   %s", sc_dump_hex(cwa_session->ssc, sizeof(cwa_session->ssc)));

	switch (sm_info->cmd)  {
	case SM_CMD_FILE_READ:
		rv = sm_iasecc_get_apdu_read_binary(ctx, sm_info, rdata);
		LOG_TEST_RET(ctx, rv, "SM IAS/ECC get APDUs: 'READ BINARY' failed");
		break;
/*
	case SM_CMD_FILE_UPDATE:
		rv = sm_iasecc_get_apdu_update_binary(ctx, sm_info, rdata);
		LOG_TEST_RET(ctx, rv, "SM IAS/ECC get APDUs: 'UPDATE BINARY' failed");
		break;
	case SM_CMD_FILE_CREATE:
		rv = sm_iasecc_get_apdu_create_file(ctx, sm_info, rdata);
		LOG_TEST_RET(ctx, rv, "SM IAS/ECC get APDUs: 'CREATE FILE' failed");
		break;
	case SM_CMD_FILE_DELETE:
		rv = sm_iasecc_get_apdu_delete_file(ctx, sm_info, rdata);
		LOG_TEST_RET(ctx, rv, "SM IAS/ECC get APDUs: 'DELETE FILE' failed");
		break;
	case SM_CMD_PIN_RESET:
		rv = sm_iasecc_get_apdu_reset_pin(ctx, sm_info, rdata);
		LOG_TEST_RET(ctx, rv, "SM IAS/ECC get APDUs: 'RESET PIN' failed");
		break;
*/
	case SM_CMD_RSA_GENERATE:
		rv = sm_iasecc_get_apdu_generate_rsa(ctx, sm_info, rdata);
		LOG_TEST_RET(ctx, rv, "SM IAS/ECC get APDUs: 'GENERATE RSA' failed");
		break;
	case SM_CMD_RSA_UPDATE:
		rv = sm_iasecc_get_apdu_update_rsa(ctx, sm_info, rdata);
		LOG_TEST_RET(ctx, rv, "SM IAS/ECC get APDUs: 'UPDATE RSA' failed");
		break;
/*
	case SM_CMD_SDO_UPDATE:
		rv = sm_iasecc_get_apdu_sdo_update(ctx, sm_info, rdata);
		LOG_TEST_RET(ctx, rv, "SM IAS/ECC get APDUs: 'SDO UPDATE' failed");
		break;
*/
	case SM_CMD_PIN_VERIFY:
		rv = sm_iasecc_get_apdu_verify_pin(ctx, sm_info, rdata);
		LOG_TEST_RET(ctx, rv, "SM IAS/ECC get APDUs: 'RAW APDU' failed");
		break;
	default:
		LOG_TEST_RET(ctx, SC_ERROR_NOT_SUPPORTED, "unsupported SM command");
	}

	LOG_FUNC_RETURN(ctx, rv);
}


/**
 * Finalize
 *
 * Decode card answer(s)
 */
int
finalize(struct sc_context *ctx, struct sm_info *sm_info, struct sc_remote_data *rdata, unsigned char *out, size_t out_len)
{
	int rv = SC_ERROR_INTERNAL;

	LOG_FUNC_CALLED(ctx);
	sc_debug(ctx, SC_LOG_DEBUG_SM, "SM finalize: out buffer(%"SC_FORMAT_LEN_SIZE_T"u) %p",
			out_len, out);
	if (!sm_info || !rdata)
		LOG_FUNC_RETURN(ctx, SC_SUCCESS);

	if (sm_info->card_type/10*10 == SC_CARD_TYPE_IASECC_BASE)
		rv = 1;
	//	rv = sm_iasecc_decode_card_data(ctx, sm_info, rdata, out, out_len);
	else
		LOG_TEST_RET(ctx, SC_ERROR_NOT_SUPPORTED, "SM finalize: cannot decode card response(s)");

	LOG_FUNC_RETURN(ctx, rv);
}

/**
 * Module Init
 *
 * Module specific initialization
 */
int
module_init(struct sc_context *ctx, char *data)
{

	return SC_SUCCESS;

}

/**
 * Module CleanUp
 *
 * Module specific cleanup
 */
int
module_cleanup(struct sc_context *ctx)
{
	return SC_SUCCESS;
}


int
test(struct sc_context *ctx, struct sm_info *info, char *out, size_t *out_len)
{
	return SC_SUCCESS;
}
